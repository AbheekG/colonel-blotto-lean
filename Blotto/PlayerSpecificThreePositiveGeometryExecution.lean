import Blotto.PlayerSpecificThreePositiveSourceCost

/-! The actual geometry continuation retains its computed environment
and descriptor once, including the raw-input/returned-table frame. -/
namespace Blotto.PlayerSpecificThreePositiveGeometryExecution
open PlayerSpecificDensePolynomial PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates PlayerSpecificAlgebraicThreeInput
open PlayerSpecificAlgebraicSegment
set_option autoImplicit false
set_option maxHeartbeats 2500000

def run (model : RationalCostModel) (root : Candidate) (a : Input) : Descriptor 3 9×ℕ :=
  let env:=PlayerSpecificThreeEnvironmentExecution.run model root a
  let table:=PlayerSpecificThreeGeometryExecution.run model root env.1
  (table.1,env.2+table.2+price model (PlayerSpecificDescriptorProgramExecution.frame root (PlayerSpecificThreeEnvironmentExecution.input a) table.1))

theorem value (model : RationalCostModel) (root : Candidate) (a : Input) :
    (run model root a).1=PlayerSpecificAlgebraicThreeGeometry.prepare model root (PlayerSpecificAlgebraicThreeInput.environment root a) := by
  simp only [run,PlayerSpecificThreeGeometryExecution.value,PlayerSpecificThreeEnvironmentExecution.value]

end Blotto.PlayerSpecificThreePositiveGeometryExecution
