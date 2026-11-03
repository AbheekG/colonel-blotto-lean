import Blotto.PlayerSpecificNestedParameterExecution

/-! Complete nested scalar/environment prices derive from the raw six
rows and algebraic extra input; no scalar/size/cost oracle is supplied. -/
namespace Blotto.PlayerSpecificNestedParameterSourceCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificAlgebraicCandidates PlayerSpecificAlgebraicNestedInput PlayerSpecificAlgebraicNestedParameterSizes
set_option autoImplicit false
set_option maxHeartbeats 2500000

def scalarCoefficient : ℕ := 137*PlayerSpecificAlgebraicExpressionFixedCost.polynomialCoefficient 8+9
def firstCoefficient : ℕ := (PlayerSpecificExpressionVectorExecution.operations PlayerSpecificNestedParameterExecution.firstPrograms+7+4+1)*
  PlayerSpecificAlgebraicExpressionFixedCost.polynomialCoefficient 3
theorem profile (C X : ℕ) (hX : 1≤X) : C*X+9≤(C+9)*X := by nlinarith only [hX]

theorem scalar_cost (root : Candidate) (a : Input) (extra : Data) (j : Fin 6) (H : ℕ)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmH : HasHeight root.polynomial H) (he : HasHeight [root.interval.lo,root.interval.hi] H)
    (hv : root.interval.lo<root.interval.hi) (hH : 2≤H) (ha : Fits root a H)
    (hExtra : Reduced root.polynomial extra ∧ HasHeight extra H) :
    (PlayerSpecificNestedParameterExecution.scalar RationalCostModel.schoolbook root a extra j).2≤scalarCoefficient*(H+19)^3 := by
  have hc:=PlayerSpecificExpressionVectorSourceCost.polynomial_cost root (environment a extra) (PlayerSpecificNestedParameterExecution.scalarProgram j)
    H 8 hm hm0 hml hmH he hv (environment_bounds root a extra H ha hExtra)
    (by intro slot; rw [PlayerSpecificNestedParameterExecution.scalarProgram,FixedArrayTable.read_ofFn]; exact RationalNestedParametersCode.scalar_depth j)
    (by intro slot; rw [PlayerSpecificNestedParameterExecution.scalarProgram,FixedArrayTable.read_ofFn]
        exact (RationalNestedParametersCode.scalarPrograms j).LiteralHeights_mono hH (RationalNestedParametersCode.scalar_literals j))
  rw [PlayerSpecificNestedParameterExecution.scalar_operations,show H+1+7+11=H+19 by omega] at hc
  have hop : (RationalNestedParametersCode.scalarPrograms j).operationBound+7+1+1≤137 := by
    have h:=RationalNestedParametersCode.scalar_operationBound j
    omega
  have hc':=hc.trans (Nat.mul_le_mul_right ((H+19)^3)
    (Nat.mul_le_mul_right (PlayerSpecificAlgebraicExpressionFixedCost.polynomialCoefficient 8) hop))
  have hp:=PlayerSpecificNestedParameterExecution.packing_cost RationalCostModel.schoolbook j
  exact (Nat.add_le_add hc' hp).trans (profile _ _ (Nat.succ_le_of_lt (pow_pos (by omega : 0<H+19) 3)))

theorem first_cost (root : Candidate) (a : Input) (extra : Data) (H : ℕ)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmH : HasHeight root.polynomial H) (he : HasHeight [root.interval.lo,root.interval.hi] H)
    (hv : root.interval.lo<root.interval.hi) (hH : 2≤H) (ha : Fits root a H)
    (hExtra : Reduced root.polynomial extra ∧ HasHeight extra H) :
    (PlayerSpecificNestedParameterExecution.firstEnvironment RationalCostModel.schoolbook root a extra).2≤firstCoefficient*(H+22)^3 := by
  have hc:=PlayerSpecificExpressionVectorSourceCost.polynomial_cost root (environment a extra) PlayerSpecificNestedParameterExecution.firstPrograms
    H 3 hm hm0 hml hmH he hv (environment_bounds root a extra H ha hExtra)
    (by intro j; rw [PlayerSpecificNestedParameterExecution.firstPrograms,FixedArrayTable.read_ofFn]; exact RationalNestedParametersCode.first_parameter_depth j)
    (by intro j; rw [PlayerSpecificNestedParameterExecution.firstPrograms,FixedArrayTable.read_ofFn]
        exact (RationalNestedParametersCode.firstParameters j).LiteralHeights_mono hH (RationalNestedParametersCode.first_parameter_literals j))
  change _≤firstCoefficient*(H+4+7+11)^3 at hc
  rw [show H+4+7+11=H+22 by omega] at hc
  exact hc

end Blotto.PlayerSpecificNestedParameterSourceCost
