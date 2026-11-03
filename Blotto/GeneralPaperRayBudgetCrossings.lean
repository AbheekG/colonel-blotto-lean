import Blotto.GeneralPaperRayTupleResidual

/-! The final batch has at most S+1 roots: each reachable high-score
affine minimum is compared with the fixed auxiliary budget. Zero slopes
are skipped, and equality remains feasible.
-/
namespace Blotto.GeneralPaperRayBudgetCrossings
open GeneralPaperRayAffine GeneralPaperRayAffineComparison GeneralPaperRayAffineMinimum GeneralPaperRayAffineScoreStep
set_option autoImplicit false
set_option maxHeartbeats 2500000

def constant (beta : ℚ) : Affine := ⟨beta,0⟩

def comparison {K : ℕ} (beta : ℚ) (c : Choice K) : Affine := difference (constant beta) c.expression

theorem comparison_value {K : ℕ} (beta : ℚ) (c : Choice K) (t : ℚ) :
    (comparison beta c).value t=beta-c.expression.value t := by
  rw [comparison,difference_value]
  simp only [constant,Affine.value,zero_mul,add_zero]

theorem comparison_iff {K : ℕ} (beta : ℚ) (c : Choice K) (t : ℚ) :
    (comparison beta c).value t≤0 ↔ beta≤c.expression.value t := by rw [comparison_value]; exact sub_nonpos

def candidate {S K : ℕ} (table : Table S K) (h : ℕ) (beta : ℚ) (s : Fin (S+1)) : Option ℚ :=
  if h<s.val then
    match table.read s with
    | none => none
    | some c => GeneralPaperRayCrossingPairs.crossing (constant beta) c.expression
  else none

def batch {S K : ℕ} (table : Table S K) (h : ℕ) (beta : ℚ) : List ℚ :=
  (List.finRange (S+1)).filterMap (candidate table h beta)

theorem batch_length {S K : ℕ} (table : Table S K) (h : ℕ) (beta : ℚ) : (batch table h beta).length≤S+1 := by
  simpa only [batch,List.length_finRange] using List.length_filterMap_le (candidate table h beta) (List.finRange (S+1))

theorem batch_complete {S K : ℕ} (table : Table S K) (h : ℕ) (beta : ℚ) (s : Fin (S+1))
    (hs : h<s.val) (c : Choice K) (hc : table.read s=some c) (hSlope : (comparison beta c).slope≠0) :
    (comparison beta c).crossing∈batch table h beta := by
  have hDifferent : (constant beta).slope≠c.expression.slope := by
    intro he
    exact hSlope (sub_eq_zero.mpr he)
  apply List.mem_filterMap.mpr
  refine ⟨s,List.mem_finRange _,?_⟩
  simp only [candidate,hs,ite_true,hc,GeneralPaperRayCrossingPairs.crossing_eq _ _ hDifferent]
  rfl

theorem budget_stable {S K : ℕ} (table : Table S K) (h : ℕ) (beta lo hi sample t : ℚ)
    (hSample : lo<sample ∧ sample<hi) (ht : lo<t ∧ t<hi)
    (hNoCross : ∀ r∈batch table h beta,¬(lo<r ∧ r<hi)) (s : Fin (S+1)) (hs : h<s.val)
    (c : Choice K) (hc : table.read s=some c) :
    beta≤c.expression.value sample ↔ beta≤c.expression.value t := by
  have hn (hp : (comparison beta c).slope≠0) := hNoCross _ (batch_complete table h beta s hs c hc hp)
  exact ⟨fun hh => (comparison_iff beta c t).mp
      (stable_nonpositive (comparison beta c) lo hi sample t hSample ht hn ((comparison_iff beta c sample).mpr hh)),
    fun hh => (comparison_iff beta c sample).mp
      (stable_nonpositive (comparison beta c) lo hi t sample ht hSample hn ((comparison_iff beta c t).mpr hh))⟩

end Blotto.GeneralPaperRayBudgetCrossings
