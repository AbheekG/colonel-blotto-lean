import Blotto.PlayerSpecificNestedParameterSourceCost

/-! Actual measured residual geometry parameters from one cached
nested input environment; each of the five output rows executes once. -/
namespace Blotto.PlayerSpecificResidualEnvironmentExecution
open PlayerSpecificDensePolynomial PlayerSpecificAlgebraicCandidates PlayerSpecificAlgebraicNestedInput
set_option autoImplicit false
set_option maxHeartbeats 2500000

def programs : FixedArrayTable 5 (RationalExpression 7) := FixedArrayTable.ofFn
  ![RationalNestedParametersCode.U,RationalNestedParametersCode.V,
    .sub RationalNestedParametersCode.M RationalNestedParametersCode.C,
    RationalNestedParametersCode.H,RationalNestedParametersCode.T]

def run (model : RationalCostModel) (root : Candidate) (a : Input) : FixedArrayTable 5 Data×ℕ :=
  PlayerSpecificExpressionVectorExecution.run model root (environment a []) programs

theorem value (model : RationalCostModel) (root : Candidate) (a : Input) :
    (run model root a).1=PlayerSpecificAlgebraicResidualEnvironment.environment root a := by
  rw [run,PlayerSpecificExpressionVectorExecution.value]
  unfold PlayerSpecificAlgebraicResidualEnvironment.environment
  congr 1
  funext j
  fin_cases j <;> simp [programs,environment,FixedArrayTable.read_ofFn,PlayerSpecificAlgebraicExpression.run,
    RationalNestedParametersCode.U,RationalNestedParametersCode.V,RationalNestedParametersCode.M,RationalNestedParametersCode.A,
    RationalNestedParametersCode.D,RationalNestedParametersCode.C,RationalNestedParametersCode.Q,RationalNestedParametersCode.T,RationalNestedParametersCode.H]

theorem depth (j : Fin 5) : (programs.read j).depth≤2 := by fin_cases j <;> decide
theorem literals (j : Fin 5) (H : ℕ) : (programs.read j).LiteralHeights H := by
  fin_cases j <;> simp [programs,FixedArrayTable.read_ofFn,RationalExpression.LiteralHeights,
    RationalNestedParametersCode.U,RationalNestedParametersCode.V,RationalNestedParametersCode.M,RationalNestedParametersCode.A,
    RationalNestedParametersCode.D,RationalNestedParametersCode.C,RationalNestedParametersCode.Q,RationalNestedParametersCode.T,RationalNestedParametersCode.H]

end Blotto.PlayerSpecificResidualEnvironmentExecution
