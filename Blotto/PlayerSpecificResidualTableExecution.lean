import Blotto.PlayerSpecificDescriptorCopySourceCost

/-! The residual environment and every three-slot weight/endpoint
program execute once, retaining their measured returns. -/
namespace Blotto.PlayerSpecificResidualTableExecution
open PlayerSpecificDensePolynomial PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates
open PlayerSpecificAlgebraicNestedInput PlayerSpecificAlgebraicSegment
set_option autoImplicit false
set_option maxHeartbeats 2500000

def weights : FixedArrayTable 3 (RationalExpression 5) := FixedArrayTable.ofFn RationalNestedResidualCode.weights
def first : FixedArrayTable 3 (FixedArrayTable 3 (RationalExpression 5)) :=
  FixedArrayTable.ofFn (fun slot => FixedArrayTable.ofFn (RationalNestedResidualCode.vertices (RationalNestedResidual.edges slot).1))
def second : FixedArrayTable 3 (FixedArrayTable 3 (RationalExpression 5)) :=
  FixedArrayTable.ofFn (fun slot => FixedArrayTable.ofFn (RationalNestedResidualCode.vertices (RationalNestedResidual.edges slot).2))

def run (model : RationalCostModel) (root : Candidate) (a : Input) : Descriptor 3 3×ℕ :=
  let env:=PlayerSpecificResidualEnvironmentExecution.run model root a
  let table:=PlayerSpecificDescriptorProgramExecution.run model root env.1 weights first second
  (table.1,env.2+table.2+price model (List.replicate 3 (.control 0)))

theorem value (model : RationalCostModel) (root : Candidate) (a : Input) :
    (run model root a).1=PlayerSpecificAlgebraicResidualTable.prepare model root a := by
  simp only [run,PlayerSpecificResidualEnvironmentExecution.value,PlayerSpecificDescriptorProgramExecution.value,
    weights,first,second,FixedArrayTable.read_ofFn,PlayerSpecificAlgebraicResidualTable.prepare]

theorem packing (model : RationalCostModel) : price model (List.replicate 3 (.control 0))=6 := rfl

end Blotto.PlayerSpecificResidualTableExecution
