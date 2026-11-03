import Blotto.PlayerSpecificFieldEquality

/-! Actual constant and negation callers inherit the complete combination
source contract on their exact executable returns. -/
namespace Blotto.PlayerSpecificFieldUnaryContract
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificSturmVariations PlayerSpecificRationalTrace
open PlayerSpecificFieldCombinationContract
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem constant_contract (model : RationalCostModel) (m : Data) (q : ℚ) (hm : Normalized m) (hm0 : m≠[])
    (hml : m.length≤4) (x : ℝ) (hx : realEvaluate m x=0) :
    let result:=constant m q
    Reduced m result.1 ∧ result.1.length≤3 ∧ realEvaluate result.1 x=(q:ℝ) ∧
      HasHeight result.1 (100000*(inputHeight m [q] []+1)) ∧
      price model result.2≤200000000*model.rat (PlayerSpecificFieldCombinationCost.width (inputHeight m [q] [])) := by
  have hc:=actual_contract model false m [q] [] hm hm0 hml (by simp) (by simp) x hx
  simpa only [constant,realEvaluate,List.foldr_cons,List.foldr_nil,Bool.false_eq_true,ite_false,mul_zero,add_zero] using hc

theorem negative_contract (model : RationalCostModel) (m a : Data) (hm : Normalized m) (hm0 : m≠[])
    (hml : m.length≤4) (hal : a.length≤3) (x : ℝ) (hx : realEvaluate m x=0) :
    let result:=negative m a
    Reduced m result.1 ∧ result.1.length≤3 ∧ realEvaluate result.1 x= -realEvaluate a x ∧
      HasHeight result.1 (100000*(inputHeight m [] a+1)) ∧
      price model result.2≤200000000*model.rat (PlayerSpecificFieldCombinationCost.width (inputHeight m [] a)) := by
  have hc:=actual_contract model true m [] a hm hm0 hml (by simp) hal x hx
  simpa only [negative,realEvaluate,List.foldr_nil,ite_true,zero_sub] using hc

end Blotto.PlayerSpecificFieldUnaryContract
