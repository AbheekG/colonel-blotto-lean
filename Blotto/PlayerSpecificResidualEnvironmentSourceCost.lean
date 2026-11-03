import Blotto.PlayerSpecificResidualEnvironmentExecution

/-! Complete residual environment source work, including the original
raw-input array, all fixed field programs and returned parameter rows. -/
namespace Blotto.PlayerSpecificResidualEnvironmentSourceCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificAlgebraicCandidates PlayerSpecificAlgebraicNestedInput PlayerSpecificAlgebraicNestedParameterSizes
set_option autoImplicit false
set_option maxHeartbeats 2500000

def coefficient : ℕ := (PlayerSpecificExpressionVectorExecution.operations PlayerSpecificResidualEnvironmentExecution.programs+7+5+1)*
  PlayerSpecificAlgebraicExpressionFixedCost.polynomialCoefficient 2

theorem cost (root : Candidate) (a : Input) (H : ℕ) (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[])
    (hml : root.polynomial.length≤4) (hmH : HasHeight root.polynomial H) (he : HasHeight [root.interval.lo,root.interval.hi] H)
    (hv : root.interval.lo<root.interval.hi) (ha : Fits root a H) :
    (PlayerSpecificResidualEnvironmentExecution.run RationalCostModel.schoolbook root a).2≤coefficient*(H+23)^3 := by
  have hc:=PlayerSpecificExpressionVectorSourceCost.polynomial_cost root (environment a []) PlayerSpecificResidualEnvironmentExecution.programs H 2
    hm hm0 hml hmH he hv (environment_bounds root a [] H ha ⟨nil_reduced _ hm0,nil_height _⟩)
    PlayerSpecificResidualEnvironmentExecution.depth (fun j => PlayerSpecificResidualEnvironmentExecution.literals j H)
  change _≤coefficient*(H+5+7+11)^3 at hc
  rw [show H+5+7+11=H+23 by omega] at hc
  exact hc

end Blotto.PlayerSpecificResidualEnvironmentSourceCost
