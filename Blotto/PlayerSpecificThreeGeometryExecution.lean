import Blotto.PlayerSpecificDescriptorProgramSourceCost

/-! The actual nine-segment three-variable formula table now executes
through the complete measured interpreter and retained table builder. -/
namespace Blotto.PlayerSpecificThreeGeometryExecution
open PlayerSpecificDensePolynomial PlayerSpecificAlgebraicCandidates RationalThreeGeometryCode
set_option autoImplicit false
set_option maxHeartbeats 2500000

def weights : FixedArrayTable 9 (RationalExpression 4) := FixedArrayTable.ofFn chosen
def first : FixedArrayTable 9 (FixedArrayTable 3 (RationalExpression 4)) :=
  FixedArrayTable.ofFn (fun slot => FixedArrayTable.ofFn (fun j => vertex (RationalThreeGeometry.edges slot).1 j))
def second : FixedArrayTable 9 (FixedArrayTable 3 (RationalExpression 4)) :=
  FixedArrayTable.ofFn (fun slot => FixedArrayTable.ofFn (fun j => vertex (RationalThreeGeometry.edges slot).2 j))

def run (model : RationalCostModel) (root : Candidate) (env : FixedArrayTable 4 Data) : PlayerSpecificAlgebraicThreeGeometry.Descriptor×ℕ :=
  PlayerSpecificDescriptorProgramExecution.run model root env weights first second

theorem value (model : RationalCostModel) (root : Candidate) (env : FixedArrayTable 4 Data) :
    (run model root env).1=PlayerSpecificAlgebraicThreeGeometry.prepare model root env := by
  simp only [run,PlayerSpecificDescriptorProgramExecution.value,weights,first,second,FixedArrayTable.read_ofFn,
    PlayerSpecificAlgebraicThreeGeometry.prepare]

def operationCount : ℕ := PlayerSpecificDescriptorProgramExecution.operations weights first second

end Blotto.PlayerSpecificThreeGeometryExecution
