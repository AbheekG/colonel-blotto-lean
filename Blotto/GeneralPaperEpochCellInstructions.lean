import Blotto.GeneralPaperEpochLevelArray

/-! Materialize one range instruction per cached cell from its exact local
level array. Partition coverage/disjointness and per-round constancy give
the cumulative code effect of this actual list construction.
-/
namespace Blotto.GeneralPaperEpochCellInstructions
open scoped BigOperators Classical
open GeneralPaperIntervalBatch
set_option autoImplicit false
set_option maxHeartbeats 3000000

abbrev Cells (n : ℕ) := FixedArrayTable n (ℕ × ℕ)

def Contains {n : ℕ} (cells : Cells n) (r : Fin n) (i : ℕ) : Prop :=
  (cells.read r).1≤ i ∧ i<(cells.read r).2

def Covers {n : ℕ} (U : ℕ) (cells : Cells n) : Prop := ∀ i<U, ∃ r, Contains cells r i

def Disjoint {n : ℕ} (cells : Cells n) : Prop := ∀ r s i, Contains cells r i → Contains cells s i → r=s

def build {n : ℕ} (cells : Cells n) (localLevels : FixedArrayTable n ℕ) : List Instruction :=
  List.ofFn (fun r => ⟨(cells.read r).1,(cells.read r).2,localLevels.read r⟩)

theorem build_length {n : ℕ} (cells : Cells n) (localLevels : FixedArrayTable n ℕ) : (build cells localLevels).length=n :=
  List.length_ofFn

theorem effect_sum (entries : List Instruction) (i : ℕ) :
    effect entries i=(entries.map (fun entry => increment entry i)).sum := by
  induction entries with
  | nil => rfl
  | cons entry rest ih => simp only [effect,List.map_cons,List.sum_cons,ih]

theorem build_effect {n : ℕ} (cells : Cells n) (localLevels : FixedArrayTable n ℕ) (i : ℕ) :
    effect (build cells localLevels) i=∑ r, if Contains cells r i then localLevels.read r else 0 := by
  rw [effect_sum]
  simp only [build,List.map_ofFn,List.sum_ofFn,Function.comp_def,increment,Contains]
  apply Finset.sum_congr rfl
  intro r _
  by_cases hLo : (cells.read r).1≤ i
  <;> by_cases hHi : i<(cells.read r).2
  <;> simp [hLo,hHi]

theorem unique_effect {n : ℕ} (cells : Cells n) (localLevels : FixedArrayTable n ℕ)
    (hDisjoint : Disjoint cells) (r : Fin n) (i : ℕ) (hContains : Contains cells r i) :
    effect (build cells localLevels) i=localLevels.read r := by
  rw [build_effect]
  calc
    _ = (if Contains cells r i then localLevels.read r else 0) := by
      apply Finset.sum_eq_single r
      · intro s _ hs
        have hn : ¬Contains cells s i := fun h => hs (hDisjoint s r i h hContains)
        simp only [hn,ite_false]
      · simp
    _ = _ := if_pos hContains

theorem cumulative_effect {n U : ℕ} (cells : Cells n) (delta : ℕ → FixedArrayTable n ℕ)
    (rowIncrement : ℕ → Fin U → ℕ) (start period : ℕ)
    (hCover : Covers U cells) (hDisjoint : Disjoint cells)
    (hDelta : ∀ t<period, ∀ r (i : Fin U), Contains cells r i.val →
      (delta t).read r=rowIncrement (start+t) i) (i : Fin U) :
    effect (build cells (GeneralPaperEpochLevelArray.execute delta period).1) i.val=
      GeneralPaperGeometricLevels.levels (fun t => rowIncrement (start+t)) period i := by
  obtain ⟨r,hr⟩ := hCover i.val i.isLt
  rw [unique_effect cells _ hDisjoint r i.val hr,GeneralPaperEpochLevelArray.execute_read]
  exact GeneralPaperEpochLevelArray.levels_agree _ _ period r i (fun t ht => hDelta t ht r i hr)

end Blotto.GeneralPaperEpochCellInstructions
