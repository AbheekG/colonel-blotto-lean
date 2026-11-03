import Blotto.PlayerSpecificResidualEnvironmentSourceCost

/-! All eight actual four-variable parameter programs execute once
over the native cached six-row environment. -/
namespace Blotto.PlayerSpecificFourParameterExecution
open PlayerSpecificDensePolynomial PlayerSpecificAlgebraicCandidates PlayerSpecificAlgebraicFourInput
set_option autoImplicit false
set_option maxHeartbeats 2500000

def programs : FixedArrayTable 8 (RationalExpression 6) := FixedArrayTable.ofFn RationalFourParametersCode.programs
def run (model : RationalCostModel) (root : Candidate) (a : Input) : FixedArrayTable 8 Data×ℕ :=
  PlayerSpecificExpressionVectorExecution.run model root (environment a) programs

theorem value (model : RationalCostModel) (root : Candidate) (a : Input) :
    (run model root a).1=PlayerSpecificAlgebraicFourInput.parameters model root a := by
  simp only [run,PlayerSpecificExpressionVectorExecution.value,programs,FixedArrayTable.read_ofFn,PlayerSpecificAlgebraicFourInput.parameters]

end Blotto.PlayerSpecificFourParameterExecution
