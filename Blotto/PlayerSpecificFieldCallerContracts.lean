import Blotto.PlayerSpecificFieldDivisionContract

/-! Explicit schoolbook bounds for all remaining exact field callers.
Together with ModularContract, AlgebraicInverseContract and priced zero,
these close the arithmetic/equality source joins; order/sign is separate. -/
namespace Blotto.PlayerSpecificFieldCallerContracts
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations
open PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 1500000

def equalityPolynomialCoefficient : ℕ := 201000000*(PlayerSpecificFieldEquality.widthCoefficient*
  PlayerSpecificFieldEquality.widthCoefficient+PlayerSpecificFieldEquality.widthCoefficient)

theorem equality_polynomial_cost (m a b : Data) (hm : Normalized m) (hm0 : m≠[])
    (hml : m.length≤4) (hal : a.length≤3) (hbl : b.length≤3) :
    (PlayerSpecificFieldEquality.run RationalCostModel.schoolbook m a b).2≤
      equalityPolynomialCoefficient*(PlayerSpecificFieldCombinationContract.inputHeight m a b+1)^2 := by
  have hc:=PlayerSpecificFieldEquality.source_cost RationalCostModel.schoolbook m a b hm hm0 hml hal hbl
  change (PlayerSpecificFieldEquality.run RationalCostModel.schoolbook m a b).2≤201000000*
    ((PlayerSpecificFieldEquality.widthCoefficient*(PlayerSpecificFieldCombinationContract.inputHeight m a b+1))*
      (PlayerSpecificFieldEquality.widthCoefficient*(PlayerSpecificFieldCombinationContract.inputHeight m a b+1))+
        PlayerSpecificFieldEquality.widthCoefficient*(PlayerSpecificFieldCombinationContract.inputHeight m a b+1)) at hc
  exact hc.trans (PlayerSpecificAlgebraicInverseContract.quadratic_profile _ _ _ (by omega))

theorem constant_polynomial_cost (m : Data) (q : ℚ) (hm : Normalized m) (hm0 : m≠[])
    (hml : m.length≤4) (x : ℝ) (hx : realEvaluate m x=0) :
    price RationalCostModel.schoolbook (PlayerSpecificFieldCombinationContract.constant m q).2≤
      PlayerSpecificFieldCombinationContract.polynomialCoefficient*
        (PlayerSpecificFieldCombinationContract.inputHeight m [q] []+1)^2 :=
  PlayerSpecificFieldCombinationContract.polynomial_cost false m [q] [] hm hm0 hml (by simp) (by simp) x hx

theorem negative_polynomial_cost (m a : Data) (hm : Normalized m) (hm0 : m≠[])
    (hml : m.length≤4) (hal : a.length≤3) (x : ℝ) (hx : realEvaluate m x=0) :
    price RationalCostModel.schoolbook (PlayerSpecificFieldCombinationContract.negative m a).2≤
      PlayerSpecificFieldCombinationContract.polynomialCoefficient*
        (PlayerSpecificFieldCombinationContract.inputHeight m [] a+1)^2 :=
  PlayerSpecificFieldCombinationContract.polynomial_cost true m [] a hm hm0 hml (by simp) hal x hx

end Blotto.PlayerSpecificFieldCallerContracts
