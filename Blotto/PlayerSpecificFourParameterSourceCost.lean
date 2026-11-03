import Blotto.PlayerSpecificFourParameterExecution

/-! Complete polynomial source prices for all actual four-variable
parameters derive from the six original retained field rows. -/
namespace Blotto.PlayerSpecificFourParameterSourceCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificAlgebraicCandidates PlayerSpecificAlgebraicFourInput
set_option autoImplicit false
set_option maxHeartbeats 2500000

def coefficient : ℕ := (PlayerSpecificExpressionVectorExecution.operations PlayerSpecificFourParameterExecution.programs+6+8+1)*
  PlayerSpecificAlgebraicExpressionFixedCost.polynomialCoefficient 12

theorem cost (root : Candidate) (a : Input) (H : ℕ) (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[])
    (hml : root.polynomial.length≤4) (hmH : HasHeight root.polynomial H) (he : HasHeight [root.interval.lo,root.interval.hi] H)
    (hv : root.interval.lo<root.interval.hi) (hH : 2≤H) (ha : Fits root a H) :
    (PlayerSpecificFourParameterExecution.run RationalCostModel.schoolbook root a).2≤coefficient*(H+25)^3 := by
  have hc:=PlayerSpecificExpressionVectorSourceCost.polynomial_cost root (environment a) PlayerSpecificFourParameterExecution.programs H 12
    hm hm0 hml hmH he hv (environment_bounds root a H ha)
    (by intro j; rw [PlayerSpecificFourParameterExecution.programs,FixedArrayTable.read_ofFn]; exact RationalFourParametersCode.depth j)
    (by intro j; rw [PlayerSpecificFourParameterExecution.programs,FixedArrayTable.read_ofFn]
        exact (RationalFourParametersCode.programs j).LiteralHeights_mono hH (RationalFourParametersCode.literals j))
  change _≤coefficient*(H+8+6+11)^3 at hc
  rw [show H+8+6+11=H+25 by omega] at hc
  exact hc

end Blotto.PlayerSpecificFourParameterSourceCost
