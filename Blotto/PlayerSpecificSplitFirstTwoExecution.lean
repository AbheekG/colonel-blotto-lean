import Blotto.PlayerSpecificFourGluingDrawSourceCost

/-! The actual split retains one denominator, both fractions and both
products once. The other two coordinates are copied with full frames. -/
namespace Blotto.PlayerSpecificSplitFirstTwoExecution
open PlayerSpecificDensePolynomial PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates
set_option autoImplicit false
set_option maxHeartbeats 2500000

def environment (a d : Data) (y : FixedArrayTable 3 Data) : FixedArrayTable 5 Data :=
  FixedArrayTable.ofFn ![a,d,y.read 0,y.read 1,y.read 2]
def run (model : RationalCostModel) (root : Candidate) (a d : Data) (y : FixedArrayTable 3 Data) : FixedArrayTable 4 Data×ℕ :=
  let denominator:=PlayerSpecificFieldCombination.run false root.polynomial a d
  let first:=PlayerSpecificFieldDivisionExecution.run model root.polynomial a denominator.1
  let second:=PlayerSpecificFieldDivisionExecution.run model root.polynomial d denominator.1
  let firstProduct:=PlayerSpecificMixtureScalarExecution.scale model root first.1 (y.read 0)
  let secondProduct:=PlayerSpecificMixtureScalarExecution.scale model root second.1 (y.read 0)
  let result:=FixedArrayTable.ofFn ![firstProduct.1,secondProduct.1,y.read 1,y.read 2]
  (result,price model denominator.2+first.2+second.2+firstProduct.2+secondProduct.2+
    price model (PlayerSpecificExpressionVectorExecution.frame root (environment a d y) result)+price model (List.replicate 7 (.control 1)))

theorem value (model : RationalCostModel) (root : Candidate) (a d : Data) (y : FixedArrayTable 3 Data) :
    (run model root a d y).1=PlayerSpecificAlgebraicSplitFirstTwo.split root a d y := by
  simp only [run,PlayerSpecificFieldCombination.value,Bool.false_eq_true,ite_false,PlayerSpecificFieldDivisionExecution.value,
    PlayerSpecificMixtureScalarExecution.scale_value,PlayerSpecificAlgebraicSplitFirstTwo.split]
theorem packing (model : RationalCostModel) : price model (List.replicate 7 (.control 1))=14 := rfl

theorem price_equation (model : RationalCostModel) (root : Candidate) (a d : Data) (y : FixedArrayTable 3 Data) :
    (run model root a d y).2=price model (PlayerSpecificFieldCombination.run false root.polynomial a d).2+
      (PlayerSpecificFieldDivisionExecution.run model root.polynomial a (PlayerSpecificAlgebraicField.plus root.polynomial a d)).2+
      (PlayerSpecificFieldDivisionExecution.run model root.polynomial d (PlayerSpecificAlgebraicField.plus root.polynomial a d)).2+
      (PlayerSpecificMixtureScalarExecution.scale model root (PlayerSpecificAlgebraicField.divide root.polynomial a (PlayerSpecificAlgebraicField.plus root.polynomial a d)) (y.read 0)).2+
      (PlayerSpecificMixtureScalarExecution.scale model root (PlayerSpecificAlgebraicField.divide root.polynomial d (PlayerSpecificAlgebraicField.plus root.polynomial a d)) (y.read 0)).2+
      price model (PlayerSpecificExpressionVectorExecution.frame root (environment a d y) (run model root a d y).1)+14 := by
  simp only [run,PlayerSpecificFieldCombination.value,Bool.false_eq_true,ite_false,PlayerSpecificFieldDivisionExecution.value,packing]

end Blotto.PlayerSpecificSplitFirstTwoExecution
