import Blotto.PlayerSpecificInitialPositivePrecision

/-! Actual positive-length comparisons at the retained root. Each test
constructs a difference polynomial and invokes the complete exact sign
backend. The vector test stops at the first failed comparison. -/
namespace Blotto.PlayerSpecificMinimumTest
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations
open PlayerSpecificRationalTrace PlayerSpecificAlgebraicReduction PlayerSpecificIsolationState
set_option autoImplicit false
set_option maxHeartbeats 2500000

def test (model : RationalCostModel) (m a : Data) (node : Interval) (q : ℚ) : Bool×ℕ :=
  let difference:=PlayerSpecificDenseExecution.subtract a [q]
  let signed:=PlayerSpecificPolynomialSignExecution.run model m difference.1 node
  (decide (signed.1≠.neg),price model difference.2+signed.2+
    price model (copyRow m++copyRow a++copyRow [node.lo,node.hi,q]++[.control 1]))

def all (model : RationalCostModel) (m : Data) (node : Interval) (q : ℚ) : List Data → Bool×ℕ
  | [] => (true,price model (copyRow [q]++[.control 0]))
  | a::rows =>
    let head:=test model m a node q
    if head.1 then
      let tail:=all model m node q rows
      (tail.1,head.2+tail.2+price model (copyRow [q]++[.control (rows.length+1),.control 1]))
    else (false,head.2+price model (copyRow [q]++[.control (rows.length+1),.control 0]))

theorem test_correct (model : RationalCostModel) (m a : Data) (node : Interval) (q : ℚ)
    (hm : Normalized m) (hirr : Irreducible (semantics m)) (hv : node.lo<node.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique m node x) :
    (test model m a node q).1=true ↔ (q:ℝ)≤realEvaluate a x := by
  have hs:=PlayerSpecificPolynomialSignExecution.correct model m
    (PlayerSpecificDenseExecution.subtract a [q]).1 node hm hirr hv x hx
  rw [PlayerSpecificDenseExecution.subtract_value,real_subtract] at hs
  have hq : realEvaluate [q] x=(q:ℝ) := by simp [realEvaluate]
  simp only [test,decide_eq_true_eq,PlayerSpecificDenseExecution.subtract_value,hs,hq,
    SignType.neg_eq_neg_one,ne_eq,sign_eq_neg_one_iff,not_lt,sub_nonneg]

theorem all_correct (model : RationalCostModel) (m : Data) (node : Interval) (q : ℚ) (rows : List Data)
    (hm : Normalized m) (hirr : Irreducible (semantics m)) (hv : node.lo<node.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique m node x) :
    (all model m node q rows).1=true ↔ ∀ a∈rows,(q:ℝ)≤realEvaluate a x := by
  induction rows with
  | nil => simp [all]
  | cons a rows ih =>
    have hc:=test_correct model m a node q hm hirr hv x hx
    simp only [all]
    split
    · rename_i h
      simpa only [List.mem_cons,forall_eq_or_imp,(hc.mp h),true_and] using ih
    · rename_i h
      simp only [Bool.false_eq_true,false_iff,List.mem_cons,forall_eq_or_imp]
      intro he
      exact h (hc.mpr he.1)

end Blotto.PlayerSpecificMinimumTest
