import Blotto.BinaryFactoryHeight
import Blotto.BinaryCachedGroupInputHeight

/-! Native route emission retains each selected multiplication and the one
mixed-pivot addition. Cached coefficient heights derive from actual lengths/
totals. Original bytes and derived primitive prices include inactive routes;
array/control/copy/ownership/physical costs remain separate. -/

namespace Blotto.BinaryGroupRouteEmissionWork
open BinaryRationalNormalization BinaryRationalEncoding BinaryRationalOpcode BinaryFactoryHeight
open scoped BigOperators

theorem patch_height {n m : ℕ} (table : FixedArrayTable n (BinaryGroupRoutes.Route m)) (s : ℕ)
    (h : ∀ j, RationalHeight (value (table.read j).2) s)
    (entries : List (Fin n × BinaryGroupRoutes.Route m))
    (he : ∀ entry ∈ entries, RationalHeight (value entry.2.2) s) :
    ∀ j, RationalHeight (value ((table.patch entries).read j).2) s := by
  induction entries generalizing table with
  | nil => exact h
  | cons entry entries ih =>
      apply ih
      · intro j
        rw [FixedArrayTable.read_write]
        split
        · exact he entry (by simp)
        · exact h j
      · intro next hn
        exact he next (by simp [hn])

theorem prepare_height {n m : ℕ} (length : FixedArrayTable n SignedWord)
    (groups : FixedArrayTable m (List (Fin n) × SignedWord))
    (hL : ∀ j, CanonicalWord (length.read j)) (hT : ∀ g, CanonicalWord (groups.read g).2)
    (s : ℕ) (hs : 3 ≤ s) (hLH : ∀ j, RationalHeight (value (length.read j)) s)
    (hTH : ∀ g, RationalHeight (value (groups.read g).2) s) :
    ∀ j, RationalHeight (value ((BinaryGroupRoutes.prepare length groups).read j).2) (expressionHeightBudget s 1) := by
  apply patch_height
  · intro j; rw [FixedArrayTable.read_ofFn]
    exact zero_height _ (height_three hs)
  · intro entry he
    obtain ⟨g,hg,he⟩ := List.mem_flatMap.mp he
    obtain ⟨j,hj,hEntry⟩ := List.mem_map.mp he
    subst entry
    rw [apply_value .div _ _ (hL j).1 (hT g).1]
    have hFirst : RationalHeight (value (length.read j)) (expressionHeightBudget s 0) := by simpa only [expressionHeightBudget_zero] using hLH j
    have hSecond : RationalHeight (value (groups.read g).2) (expressionHeightBudget s 0) := by simpa only [expressionHeightBudget_zero] using hTH g
    exact hFirst.div_level hSecond

def emitWithWork {n m : ℕ} (routes : FixedArrayTable n (BinaryGroupRoutes.Route m)) (row : FixedArrayTable m SignedWord) :
    FixedArrayTable n SignedWord × ℕ :=
  let cells := FixedArrayTable.ofFn (fun j =>
    let route := routes.read j
    match route.1 with
    | none => (zero,0)
    | some g => applyWithWork .mul route.2 (row.read g))
  (FixedArrayTable.ofFn (fun j => (cells.read j).1),∑ j, (cells.read j).2)

theorem emitWithWork_state {n m : ℕ} (routes : FixedArrayTable n (BinaryGroupRoutes.Route m)) (row : FixedArrayTable m SignedWord) :
    (emitWithWork routes row).1 = BinaryGroupRoutes.emit routes row := by
  unfold emitWithWork BinaryGroupRoutes.emit
  simp only [FixedArrayTable.read_ofFn]
  congr 1
  funext j
  cases (routes.read j).1 <;> rfl

theorem emit_height {n m : ℕ} (routes : FixedArrayTable n (BinaryGroupRoutes.Route m)) (row : FixedArrayTable m SignedWord)
    (hC : ∀ j, CanonicalWord (routes.read j).2) (hRow : ∀ g, CanonicalWord (row.read g))
    (s : ℕ) (hs : 3 ≤ s) (hR : ∀ j, RationalHeight (value (routes.read j).2) s)
    (hH : ∀ g, RationalHeight (value (row.read g)) s) (j : Fin n) :
    RationalHeight (value ((BinaryGroupRoutes.emit routes row).read j)) (expressionHeightBudget s 1) := by
  rw [BinaryGroupRoutes.emit,FixedArrayTable.read_ofFn]
  split
  · exact zero_height _ (height_three hs)
  · rename_i g hg
    rw [apply_value .mul _ _ (hC j).1 (hRow g).1]
    have hFirst : RationalHeight (value (routes.read j).2) (expressionHeightBudget s 0) := by simpa only [expressionHeightBudget_zero] using hR j
    have hSecond : RationalHeight (value (row.read g)) (expressionHeightBudget s 0) := by simpa only [expressionHeightBudget_zero] using hH g
    exact hFirst.mul_level hSecond

theorem emitWithWork_bound {n m : ℕ} (routes : FixedArrayTable n (BinaryGroupRoutes.Route m)) (row : FixedArrayTable m SignedWord)
    (hC : ∀ j, CanonicalWord (routes.read j).2) (hRow : ∀ g, CanonicalWord (row.read g))
    (s : ℕ) (hR : ∀ j, RationalHeight (value (routes.read j).2) s) (hH : ∀ g, RationalHeight (value (row.read g)) s) :
    (emitWithWork routes row).2 ≤ n * opcodeBound s := by
  have hEach : ∀ j : Fin n, (match (routes.read j).1 with
    | none => (zero,0)
    | some g => applyWithWork .mul (routes.read j).2 (row.read g)).2 ≤ opcodeBound s := by
    intro j
    split
    · exact Nat.zero_le _
    · rename_i g hg
      exact opcode_bound .mul _ _ (hC j) (hRow g) s (hR j) (hH g)
  unfold emitWithWork
  simp only [FixedArrayTable.read_ofFn]
  change (∑ j : Fin n, (match (routes.read j).1 with
    | none => (zero,0)
    | some g => applyWithWork .mul (routes.read j).2 (row.read g)).2) ≤ _
  calc
    _ ≤ ∑ _j : Fin n, opcodeBound s := Finset.sum_le_sum (fun j _ => hEach j)
    _ = n * opcodeBound s := by simp

def emitMixedWithWork {n m : ℕ} (routes : FixedArrayTable n (BinaryGroupRoutes.Route m)) (pivot : Fin n) (row : FixedArrayTable (m+1) SignedWord) :
    FixedArrayTable n SignedWord × ℕ :=
  let uniform := FixedArrayTable.ofFn (fun g : Fin m => row.read g.castSucc)
  let old := emitWithWork routes uniform
  let extra := applyWithWork .add (old.1.read pivot) (row.read (Fin.last m))
  (old.1.write pivot extra.1,old.2 + extra.2)

theorem emitMixedWithWork_state {n m : ℕ} (routes : FixedArrayTable n (BinaryGroupRoutes.Route m)) (pivot : Fin n) (row : FixedArrayTable (m+1) SignedWord) :
    (emitMixedWithWork routes pivot row).1 = BinaryGroupRoutes.emitMixed routes pivot row := by
  unfold emitMixedWithWork BinaryGroupRoutes.emitMixed
  simp only [emitWithWork_state,applyWithWork_state]

theorem opcodeBound_mono {s t : ℕ} (h : s ≤ t) : opcodeBound s ≤ opcodeBound t := by
  unfold opcodeBound
  gcongr

theorem emitMixedWithWork_bound {n m : ℕ} (routes : FixedArrayTable n (BinaryGroupRoutes.Route m)) (pivot : Fin n) (row : FixedArrayTable (m+1) SignedWord)
    (hC : ∀ j, CanonicalWord (routes.read j).2) (hRow : ∀ g, CanonicalWord (row.read g))
    (s : ℕ) (hs : 3 ≤ s) (hR : ∀ j, RationalHeight (value (routes.read j).2) s) (hH : ∀ g, RationalHeight (value (row.read g)) s) :
    (emitMixedWithWork routes pivot row).2 ≤ (n + 1) * opcodeBound (expressionHeightBudget s 1) := by
  let uniform := FixedArrayTable.ofFn (fun g : Fin m => row.read g.castSucc)
  have hc : ∀ g, CanonicalWord (uniform.read g) := by intro g; rw [FixedArrayTable.read_ofFn]; exact hRow _
  have hh : ∀ g, RationalHeight (value (uniform.read g)) s := by intro g; rw [FixedArrayTable.read_ofFn]; exact hH _
  have he := emitWithWork_bound routes uniform hC hc s hR hh
  have hCan := BinaryGroupRoutes.emit_canonical routes uniform hC hc
  have hHeight := emit_height routes uniform hC hc s hs hR hh pivot
  have hExtra := opcode_bound .add ((BinaryGroupRoutes.emit routes uniform).read pivot) (row.read (Fin.last m))
    (hCan pivot) (hRow _) _ hHeight ((hH _).mono (expressionHeightBudget_ge_input s 1))
  have hp := Nat.mul_le_mul_left n (opcodeBound_mono (expressionHeightBudget_ge_input s 1))
  unfold emitMixedWithWork
  dsimp only
  rw [emitWithWork_state]
  change (emitWithWork routes uniform).2 + _ ≤ _
  nlinarith

def emitOptionWithWork {n m : ℕ} (routes : FixedArrayTable n (BinaryGroupRoutes.Route m)) (rows : Option (FixedArrayTable m SignedWord)) :
    Option (FixedArrayTable n SignedWord) × ℕ :=
  match rows with
  | none => (none,0)
  | some row => let emitted := emitWithWork routes row; (some emitted.1,emitted.2)

theorem emitOptionWithWork_state {n m : ℕ} (routes : FixedArrayTable n (BinaryGroupRoutes.Route m)) (rows : Option (FixedArrayTable m SignedWord)) :
    (emitOptionWithWork routes rows).1 = rows.map (BinaryGroupRoutes.emit routes) := by
  cases rows <;> simp only [emitOptionWithWork,Option.map_none,Option.map_some,emitWithWork_state]

def emitMixedOptionWithWork {n m : ℕ} (routes : FixedArrayTable n (BinaryGroupRoutes.Route m)) (pivot : Fin n) (rows : Option (FixedArrayTable (m+1) SignedWord)) :
    Option (FixedArrayTable n SignedWord) × ℕ :=
  match rows with
  | none => (none,0)
  | some row => let emitted := emitMixedWithWork routes pivot row; (some emitted.1,emitted.2)

theorem emitMixedOptionWithWork_state {n m : ℕ} (routes : FixedArrayTable n (BinaryGroupRoutes.Route m)) (pivot : Fin n) (rows : Option (FixedArrayTable (m+1) SignedWord)) :
    (emitMixedOptionWithWork routes pivot rows).1 = rows.map (BinaryGroupRoutes.emitMixed routes pivot) := by
  cases rows <;> simp only [emitMixedOptionWithWork,Option.map_none,Option.map_some,emitMixedWithWork_state]

theorem emitOptionWithWork_bound {n m : ℕ} (routes : FixedArrayTable n (BinaryGroupRoutes.Route m)) (rows : Option (FixedArrayTable m SignedWord))
    (hC : ∀ j, CanonicalWord (routes.read j).2)
    (hRows : ∀ row, rows = some row → ∀ g, CanonicalWord (row.read g))
    (s : ℕ) (hR : ∀ j, RationalHeight (value (routes.read j).2) s)
    (hH : ∀ row, rows = some row → ∀ g, RationalHeight (value (row.read g)) s) :
    (emitOptionWithWork routes rows).2 ≤ n * opcodeBound s := by
  cases he : rows with
  | none => exact Nat.zero_le _
  | some row => exact emitWithWork_bound routes row hC (hRows row he) s hR (hH row he)

theorem emitMixedOptionWithWork_bound {n m : ℕ} (routes : FixedArrayTable n (BinaryGroupRoutes.Route m)) (pivot : Fin n) (rows : Option (FixedArrayTable (m+1) SignedWord))
    (hC : ∀ j, CanonicalWord (routes.read j).2)
    (hRows : ∀ row, rows = some row → ∀ g, CanonicalWord (row.read g))
    (s : ℕ) (hs : 3 ≤ s) (hR : ∀ j, RationalHeight (value (routes.read j).2) s)
    (hH : ∀ row, rows = some row → ∀ g, RationalHeight (value (row.read g)) s) :
    (emitMixedOptionWithWork routes pivot rows).2 ≤ (n+1) * opcodeBound (expressionHeightBudget s 1) := by
  cases he : rows with
  | none => exact Nat.zero_le _
  | some row => exact emitMixedWithWork_bound routes pivot row hC (hRows row he) s hs hR (hH row he)

end Blotto.BinaryGroupRouteEmissionWork
