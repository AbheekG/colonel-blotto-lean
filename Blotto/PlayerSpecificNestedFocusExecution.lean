import Blotto.PlayerSpecificNestedSpecDrawSourceCost

/-! Terminal focus selection evaluates only reached fractional tests
and retains the selected finite coordinate for later restoration. -/
namespace Blotto.PlayerSpecificNestedFocusExecution
open PlayerSpecificDensePolynomial PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates PlayerSpecificAlgebraicNestedTerminalInput
set_option autoImplicit false
set_option maxHeartbeats 2500000

def frame (j : Fin 3) : Trace := [.control 1,.control 1,.control j.val]
def run (model : RationalCostModel) (root : Candidate) (a : Input) : Fin 3×ℕ :=
  let first:=PlayerSpecificAlgebraicComparisonExecution.active model root (a.capacity.read 0) (a.resource.read 0)
  if first.1 then (0,first.2+price model (frame 0)) else
    let second:=PlayerSpecificAlgebraicComparisonExecution.active model root (a.capacity.read 1) (a.resource.read 1)
    let result:Fin 3:=if second.1 then 1 else 2
    (result,first.2+second.2+price model (frame result))

theorem value (model : RationalCostModel) (root : Candidate) (a : Input) :
    (run model root a).1=PlayerSpecificAlgebraicNestedTerminalInput.focus model root a := by
  simp only [run,PlayerSpecificAlgebraicComparisonExecution.active_value,PlayerSpecificAlgebraicNestedTerminalInput.focus]
  split <;> rfl
theorem packing_cost (model : RationalCostModel) (j : Fin 3) : price model (frame j)≤7 := by
  fin_cases j <;> simp only [frame,price,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Event.price] <;> decide

end Blotto.PlayerSpecificNestedFocusExecution
