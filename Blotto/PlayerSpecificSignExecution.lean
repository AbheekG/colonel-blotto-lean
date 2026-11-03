import Blotto.PlayerSpecificSignMidpointExecution

/-! Complete executing cached sign entry. All preparation is performed
once in the nonzero branch, and the actual cached data feed retagging,
selected-path refinement and midpoint/sign execution directly. -/
namespace Blotto.PlayerSpecificSignExecution
open SignType PlayerSpecificDensePolynomial PlayerSpecificIsolationState PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 2000000

def run (model : RationalCostModel) (m a : Data) (node : Interval) : SignType×ℕ :=
  let zero:=PlayerSpecificAlgebraicZeroExecution.run model a
  if zero.1 then
    (0,zero.2+price model (copyRow m)+price model (copyRow a)+price model (copyRow [node.lo,node.hi])+price model [.control 0])
  else
    let computed:=PlayerSpecificSignPreparation.run model m a node
    let cached : Prepared m:=⟨computed.1.polynomials.rows,PlayerSpecificSignPreparation.rows_value model m a node⟩
    let initial:=PlayerSpecificSignRetagExecution.run cached node
    let selected:=PlayerSpecificSelectedExecution.run model cached computed.1.controls.depth initial.1
    let signed:=PlayerSpecificSignMidpointExecution.run a selected.1
    (signed.1,zero.2+computed.2+price model initial.2+selected.2+price model signed.2+
      price model (copyRow m)+price model (copyRow a)+price model (copyRow computed.1.unit)+
      price model (PlayerSpecificSturmExecution.copyRows computed.1.polynomials.rows)+
      PlayerSpecificSignPreparation.copy computed.1+price model [.control 1])

theorem value (model : RationalCostModel) (m a : Data) (node : Interval) :
    (run model m a node).1=PlayerSpecificAlgebraicSign.run m a node := by
  rw [run,PlayerSpecificAlgebraicSign.run]
  simp only [PlayerSpecificAlgebraicZeroExecution.run,PlayerSpecificAlgebraicZero.run,decide_eq_true_eq]
  split
  · rfl
  · simp only [PlayerSpecificSignMidpointExecution.value,PlayerSpecificSelectedExecution.value,
      PlayerSpecificSignRetagExecution.value,(PlayerSpecificSignPreparation.control_values model m a node).2.2.2,
      PlayerSpecificRootExecution.prepared_eq,PlayerSpecificAlgebraicSign.leaf]

end Blotto.PlayerSpecificSignExecution
