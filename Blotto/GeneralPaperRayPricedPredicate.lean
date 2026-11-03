import Blotto.GeneralPaperRayCrossingRefinement

/-! The on-demand crossing predicate executes the priced complete score
query and one weak budget test. The actual prepared score matrix supplies
its fixed scores; each probe materializes costs and executes the DP once.
-/
namespace Blotto.GeneralPaperRayPricedPredicate
open RationalOrderCell GeneralPaperExactScoreDP GeneralPaperRayAnchorCosts
set_option autoImplicit false
set_option maxHeartbeats 2500000

def query {m K : ℕ} (matrix : FixedArrayTable m (Field K)) (x w : Variable m K → ℚ)
    (S h : ℕ) (beta t : ℚ) : Bool × ℕ :=
  let result := GeneralPaperRayQueryWork.minimumRun matrix x w t S h
  let accepted := match result.1 with
    | none => true
    | some chosen => decide (beta≤chosen.cost)
  (accepted,result.2+8)

theorem query_data {m K : ℕ} (matrix : FixedArrayTable m (Field K)) (x w : Variable m K → ℚ)
    (S h : ℕ) (beta t : ℚ) : (query matrix x w S h beta t).1=
      GeneralPaperRayHighMinimum.passes (GeneralPaperRayQueryWork.scores matrix) (costs x w t) S h beta := by
  simp only [query,GeneralPaperRayQueryWork.minimum_data,GeneralPaperRayHighMinimum.passes]
  rfl

theorem query_work {m K : ℕ} (matrix : FixedArrayTable m (Field K)) (x w : Variable m K → ℚ)
    (S h : ℕ) (beta t : ℚ) : (query matrix x w S h beta t).2≤1024*(m+1)*(K+1)*(S+1)+8 := by
  exact Nat.add_le_add_right (GeneralPaperRayQueryWork.minimum_work matrix x w t S h) 8

theorem actual_data {T m K : ℕ} (scoreDepth : ℕ) (d : GeneralPaperDictionary.Dictionary T m K)
    (v : RationalFieldSelector m) (S : ℕ) (hK : 0<K) (hCap : S<2^scoreDepth)
    (x w : Variable m K → ℚ) (h : ℕ) (beta t : ℚ) :
    (query (GeneralPaperScoreMatrixWork.matrixRun scoreDepth d v S).1 x w S h beta t).1=
      GeneralPaperRayFeasibility.test v S h beta x w t := by
  rw [query_data,GeneralPaperRayInitialQuery.actual_scores scoreDepth d v S hK hCap]
  rfl

end Blotto.GeneralPaperRayPricedPredicate
