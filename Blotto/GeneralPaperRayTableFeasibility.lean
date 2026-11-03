import Blotto.GeneralPaperRayBudgetCrossings

/-! The fixed affine minimum table decides all original high-tuple
inequalities on its valid interval. Actual normalized scores derive the
full score cap; the final budget batch fixes feasibility throughout its
remaining open bracket.
-/
namespace Blotto.GeneralPaperRayTableFeasibility
open RationalOrderCell GeneralPaperRayAffineMinimum GeneralPaperRayAffineScoreStep GeneralPaperRayAnchorCosts
open GeneralPaperRayHighSound GeneralPaperRayBudgetCrossings GeneralPaperStrictScore
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 3500000

def TableFeasible {S K : ℕ} (table : Table S K) (h : ℕ) (beta t : ℚ) : Prop :=
  ∀ s,h<s.val → ∀ c,table.read s=some c → beta≤c.expression.value t

theorem high_iff {m S K : ℕ} (scores : Fin m → Fin K → ℕ) (x w : Variable m K → ℚ)
    (table : Table S K) (h : ℕ) (beta t : ℚ)
    (hCap : ∀ labels : Fin m → Fin K,(∑ j,scores j (labels j))≤S)
    (hBest : ∀ s,GeneralPaperMinimum.Best (GeneralPaperExactScoreDP.Fits
      (GeneralPaperExactScoreDP.fields scores (costs x w t)) s.val) ((tableAt table t).read s)) :
    TableFeasible table h beta t ↔ HighFeasible scores (costs x w t) h beta := by
  constructor
  · intro hf labels hl
    let s : Fin (S+1) := ⟨∑ j,scores j (labels j),by have hh := hCap labels; omega⟩
    let witness : GeneralPaperMinimum.Selection K := ⟨∑ j,costs x w t j (labels j),List.ofFn labels⟩
    have hFits := GeneralPaperExactScoreDP.fits_of_tuple scores (costs x w t) labels
    have hb := hBest s
    rw [tableAt,FixedArrayTable.read_ofFn] at hb
    cases hc : table.read s with
    | none => rw [hc] at hb; exact (hb witness hFits).elim
    | some c =>
      rw [hc] at hb
      exact (hf s hl c hc).trans (hb.2 witness hFits)
  · intro hf s hs c hc
    have hb := hBest s
    rw [tableAt,FixedArrayTable.read_ofFn,hc] at hb
    obtain ⟨labels,hScore,hCost,_⟩ := GeneralPaperExactScoreDP.tuple_of_fits scores (costs x w t) s.val (c.atPoint t) hb.1
    have hh := hf labels (by omega)
    rwa [hCost] at hh

theorem test_iff {m S K : ℕ} (v : RationalFieldSelector m) (hK : 0<K) (x w : Variable m K → ℚ)
    (table : Table S K) (h : ℕ) (beta t : ℚ)
    (hBest : ∀ s,GeneralPaperMinimum.Best (GeneralPaperExactScoreDP.Fits
      (GeneralPaperExactScoreDP.fields (score v S) (costs x w t)) s.val) ((tableAt table t).read s)) :
    GeneralPaperRayFeasibility.test v S h beta x w t=true ↔ TableFeasible table h beta t := by
  have hh := GeneralPaperRayHighSound.passes_iff (score v S) (costs x w t) S h
    (fun labels => GeneralPaperComputedThreshold.totalScore_le v S hK labels) beta
  exact hh.trans (high_iff (score v S) x w table h beta t
    (fun labels => GeneralPaperComputedThreshold.totalScore_le v S hK labels) hBest).symm

theorem table_stable {S K : ℕ} (table : Table S K) (h : ℕ) (beta lo hi sample t : ℚ)
    (hSample : lo<sample ∧ sample<hi) (ht : lo<t ∧ t<hi)
    (hNoCross : ∀ r∈batch table h beta,¬(lo<r ∧ r<hi)) :
    TableFeasible table h beta sample ↔ TableFeasible table h beta t := by
  constructor
  · intro hf s hs c hc
    exact (budget_stable table h beta lo hi sample t hSample ht hNoCross s hs c hc).mp (hf s hs c hc)
  · intro hf s hs c hc
    exact (budget_stable table h beta lo hi sample t hSample ht hNoCross s hs c hc).mpr (hf s hs c hc)

end Blotto.GeneralPaperRayTableFeasibility
