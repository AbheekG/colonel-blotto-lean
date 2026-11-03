import Blotto.PlayerSpecificNestedFocusSourceCost

/-! Each reached terminal endpoint uses one reduced-field equality,
retains its selected original row and prices the copied arrays/index. -/
namespace Blotto.PlayerSpecificNestedTerminalEndpointExecution
open PlayerSpecificDensePolynomial PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates PlayerSpecificAlgebraicNestedTerminalInput
set_option autoImplicit false
set_option maxHeartbeats 2500000

def environment (a : Input) (j : Fin 3) : FixedArrayTable 3 Data :=
  FixedArrayTable.ofFn ![a.long.read j,a.short.read j,a.resource.read j]
def frame (root : Candidate) (a : Input) (j : Fin 3) (result : Data) : Trace :=
  PlayerSpecificExpressionVectorExecution.frame root (environment a j) (FixedArrayTable.ofFn (fun _ : Fin 1 => result))
def run (model : RationalCostModel) (root : Candidate) (a : Input) (j : Fin 3) : Data×ℕ :=
  let tested:=PlayerSpecificAlgebraicEqualityExecution.run model root.polynomial (a.resource.read j) []
  let result:=if tested.1 then a.long.read j else a.short.read j
  (result,tested.2+price model (frame root a j result)+price model [.control 1,.control j.val])

theorem value (model : RationalCostModel) (root : Candidate) (a : Input) (j : Fin 3) :
    (run model root a j).1=PlayerSpecificAlgebraicNestedTerminalInput.endpoint root a j := by
  simp only [run,PlayerSpecificAlgebraicEqualityExecution.value,PlayerSpecificAlgebraicNestedTerminalInput.endpoint]
theorem packing_cost (model : RationalCostModel) (j : Fin 3) : price model [.control 1,.control j.val]≤6 := by
  simp only [price,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Event.price]
  have h1 : binaryWordWidth 1=1 := by decide
  rw [h1]
  have h:=control_width j.val
  have hj:=j.isLt
  omega
theorem price_equation (model : RationalCostModel) (root : Candidate) (a : Input) (j : Fin 3) :
    (run model root a j).2=(PlayerSpecificAlgebraicEqualityExecution.run model root.polynomial (a.resource.read j) []).2+
      price model (frame root a j (run model root a j).1)+price model [.control 1,.control j.val] := by
  simp only [run]

end Blotto.PlayerSpecificNestedTerminalEndpointExecution
