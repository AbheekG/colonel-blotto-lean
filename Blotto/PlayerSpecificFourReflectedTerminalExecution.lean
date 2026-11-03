import Blotto.PlayerSpecificFourReflectedPathSourceCost
import Blotto.PlayerSpecificAlgebraicFourReflectedTerminal

/-! The reached resource state is copied into the complete terminal
record once, with all source and return arrays charged. -/
namespace Blotto.PlayerSpecificFourReflectedTerminalExecution
open PlayerSpecificDensePolynomial PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates
set_option autoImplicit false
set_option maxHeartbeats 2500000

def fields (a : PlayerSpecificAlgebraicNestedTerminalInput.Input) : FixedArrayTable 13 Data := FixedArrayTable.ofFn
  ![a.budget,a.long.read 0,a.long.read 1,a.long.read 2,
    a.short.read 0,a.short.read 1,a.short.read 2,
    a.capacity.read 0,a.capacity.read 1,a.capacity.read 2,
    a.resource.read 0,a.resource.read 1,a.resource.read 2]
def packing : Trace := List.replicate 14 (.control 1)

def run (model : RationalCostModel) (root : Candidate)
    (p : PlayerSpecificAlgebraicFourReflectedInput.Prepared)
    (s : PlayerSpecificAlgebraicResourceState.State 3) :
    PlayerSpecificAlgebraicNestedTerminalInput.Input×ℕ :=
  let result:=PlayerSpecificAlgebraicFourReflectedTerminal.input p s
  (result,price model (PlayerSpecificExpressionVectorExecution.frame root
    (PlayerSpecificFourReflectedInputExecution.fields p) (fields result))+price model packing)

theorem value (model : RationalCostModel) (root : Candidate)
    (p : PlayerSpecificAlgebraicFourReflectedInput.Prepared)
    (s : PlayerSpecificAlgebraicResourceState.State 3) :
    (run model root p s).1=PlayerSpecificAlgebraicFourReflectedTerminal.input p s := rfl

theorem packing_cost (model : RationalCostModel) : price model packing=28 := rfl

end Blotto.PlayerSpecificFourReflectedTerminalExecution
