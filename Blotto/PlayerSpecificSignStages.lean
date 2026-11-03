import Blotto.PlayerSpecificSignExecution

/-! Proof-only component views of the cached sign entry. The public
executing entry computes the cache once and does not call these views. -/
namespace Blotto.PlayerSpecificSignStages
open PlayerSpecificDensePolynomial PlayerSpecificIsolationState
set_option autoImplicit false
set_option maxHeartbeats 1500000

def cache (model : RationalCostModel) (m a : Data) (node : Interval) := PlayerSpecificSignPreparation.run model m a node
def prepared (model : RationalCostModel) (m a : Data) (node : Interval) : Prepared m :=
  ⟨(cache model m a node).1.polynomials.rows,PlayerSpecificSignPreparation.rows_value model m a node⟩
def initial (model : RationalCostModel) (m a : Data) (node : Interval) :=
  PlayerSpecificSignRetagExecution.run (prepared model m a node) node
def selected (model : RationalCostModel) (m a : Data) (node : Interval) :=
  PlayerSpecificSelectedExecution.run model (prepared model m a node) (cache model m a node).1.controls.depth
    (initial model m a node).1
def signed (model : RationalCostModel) (m a : Data) (node : Interval) :=
  PlayerSpecificSignMidpointExecution.run a (selected model m a node).1

theorem prepared_value (model : RationalCostModel) (m a : Data) (node : Interval) : prepared model m a node=prepare m :=
  PlayerSpecificRootExecution.prepared_eq _
theorem initial_value (model : RationalCostModel) (m a : Data) (node : Interval) :
    (initial model m a node).1=PlayerSpecificSignEnclosure.retag (prepare m) node := by
  rw [initial,PlayerSpecificSignRetagExecution.value,prepared_value]
theorem depth_value (model : RationalCostModel) (m a : Data) (node : Interval) :
    (cache model m a node).1.controls.depth=PlayerSpecificSignPrecision.depth m a node :=
  (PlayerSpecificSignPreparation.control_values model m a node).2.2.2
theorem selected_value (model : RationalCostModel) (m a : Data) (node : Interval) :
    (selected model m a node).1=PlayerSpecificAlgebraicSign.leaf m a node := by
  rw [selected,PlayerSpecificSelectedExecution.value,prepared_value,depth_value,initial_value]
  rfl

end Blotto.PlayerSpecificSignStages
