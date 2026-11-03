import Blotto.PlayerSpecificFieldCombinationCost

/-! Complete original-input reduced addition/subtraction and their
quadratic schoolbook source price on the same actual return. -/
namespace Blotto.PlayerSpecificFieldCombinationContract
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificSturmVariations PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 2000000

def inputHeight (m a b : Data) : ℕ := PlayerSpecificModularContract.inputHeight m a b
def polynomialCoefficient : ℕ := 200000000*(PlayerSpecificFieldCombinationCost.widthCoefficient*
  PlayerSpecificFieldCombinationCost.widthCoefficient+PlayerSpecificFieldCombinationCost.widthCoefficient)

theorem input_heights (m a b : Data) : HasHeight m (inputHeight m a b) ∧ HasHeight a (inputHeight m a b) ∧
    HasHeight b (inputHeight m a b) ∧ 1 ≤ inputHeight m a b := by
  have hh:=PlayerSpecificModularContract.input_heights m a b
  exact ⟨hh.1,hh.2.1,hh.2.2,by unfold inputHeight PlayerSpecificModularContract.inputHeight; omega⟩

theorem actual_contract (model : RationalCostModel) (difference : Bool) (m a b : Data)
    (hm : Normalized m) (hm0 : m≠[]) (hml : m.length≤4) (hal : a.length≤3) (hbl : b.length≤3)
    (x : ℝ) (hx : realEvaluate m x=0) :
    let result:=PlayerSpecificFieldCombination.run difference m a b
    Reduced m result.1 ∧ result.1.length≤3 ∧
      realEvaluate result.1 x=(if difference then realEvaluate a x-realEvaluate b x else realEvaluate a x+realEvaluate b x) ∧
      HasHeight result.1 (100000*(inputHeight m a b+1)) ∧
      price model result.2≤200000000*model.rat (PlayerSpecificFieldCombinationCost.width (inputHeight m a b)) := by
  have hi:=input_heights m a b
  have hr:=PlayerSpecificFieldCombination.reduced difference m a b hm hm0
  refine ⟨hr,by have hl:=hr.2; omega,PlayerSpecificFieldCombination.real_value difference m a b x hx,?_,?_⟩
  · exact PlayerSpecificFieldCombination.bounds difference m a b _ hi.1 hi.2.1 hi.2.2.1 hml hal hbl
  · exact PlayerSpecificFieldCombinationCost.run_cost model difference m a b hm hm0 hml _ hi.1 hi.2.1 hi.2.2.1 hi.2.2.2 hal hbl

theorem polynomial_cost (difference : Bool) (m a b : Data) (hm : Normalized m) (hm0 : m≠[])
    (hml : m.length≤4) (hal : a.length≤3) (hbl : b.length≤3) (x : ℝ) (hx : realEvaluate m x=0) :
    price RationalCostModel.schoolbook (PlayerSpecificFieldCombination.run difference m a b).2≤
      polynomialCoefficient*(inputHeight m a b+1)^2 := by
  have hc:=(actual_contract RationalCostModel.schoolbook difference m a b hm hm0 hml hal hbl x hx).2.2.2.2
  change price RationalCostModel.schoolbook (PlayerSpecificFieldCombination.run difference m a b).2≤200000000*
    ((PlayerSpecificFieldCombinationCost.widthCoefficient*(inputHeight m a b+1))*
      (PlayerSpecificFieldCombinationCost.widthCoefficient*(inputHeight m a b+1))+
        PlayerSpecificFieldCombinationCost.widthCoefficient*(inputHeight m a b+1)) at hc
  exact hc.trans (PlayerSpecificAlgebraicInverseContract.quadratic_profile _ _ _ (by omega))

def constant (m : Data) (q : ℚ) : Data×Trace := PlayerSpecificFieldCombination.run false m [q] []
def negative (m a : Data) : Data×Trace := PlayerSpecificFieldCombination.run true m [] a

theorem constant_value (m : Data) (q : ℚ) : (constant m q).1=PlayerSpecificAlgebraicField.constant m q := by
  rw [constant,PlayerSpecificFieldCombination.value]
  rfl
theorem negative_value (m a : Data) : (negative m a).1=PlayerSpecificAlgebraicField.negative m a := by
  rw [negative,PlayerSpecificFieldCombination.value]
  rfl

end Blotto.PlayerSpecificFieldCombinationContract
