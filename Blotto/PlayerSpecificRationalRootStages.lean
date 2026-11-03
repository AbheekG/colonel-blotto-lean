import Blotto.PlayerSpecificRationalRootExecution

/-! Component views used only to state small proofs about the executing
entry. The public entry keeps its original single cached preparation; it
does not call these views as additional runtime computations. -/
namespace Blotto.PlayerSpecificRationalRootStages
open PlayerSpecificDensePolynomial PlayerSpecificIsolationState PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 300000

def cache (model : RationalCostModel) (p : Data) : PlayerSpecificReconstructionCache.Result :=
  (PlayerSpecificReconstructionCache.run model p).1
def prepared (model : RationalCostModel) (p : Data) : Prepared p :=
  ⟨(cache model p).isolation.polynomials.rows,PlayerSpecificRationalRootExecution.rows_correct model p⟩
def initial (model : RationalCostModel) (p : Data) : Interval×Trace :=
  PlayerSpecificInitialExecution.run (prepared model p) (cache model p).isolation.magnitude
def forest (model : RationalCostModel) (p : Data) : List Interval×Trace :=
  PlayerSpecificForestExecution.run (prepared model p) (cache model p).depth (initial model p).1
def roots (model : RationalCostModel) (p : Data) : Data×ℕ :=
  PlayerSpecificRationalRootRows.run model p (cache model p) (forest model p).1

theorem magnitude_value (model : RationalCostModel) (p : Data) :
    (cache model p).isolation.magnitude=PlayerSpecificRootMagnitude.rootBound p :=
  PlayerSpecificReconstructionLeafBounds.magnitude_value model p

theorem depth_value (model : RationalCostModel) (p : Data) :
    (cache model p).depth=PlayerSpecificReconstructionPrecision.depth p :=
  PlayerSpecificReconstructionCache.depth_value model p

theorem initial_value (model : RationalCostModel) (p : Data) :
    (initial model p).1=PlayerSpecificRootMagnitude.initial p (prepared model p) := by
  rw [initial,PlayerSpecificInitialExecution.value,magnitude_value]
  rfl

theorem forest_value (model : RationalCostModel) (p : Data) :
    (forest model p).1=PlayerSpecificRationalRoots.intervals p := by
  rw [forest,PlayerSpecificForestExecution.value,depth_value,initial_value,
    PlayerSpecificRootExecution.prepared_eq (prepared model p)]
  rfl

end Blotto.PlayerSpecificRationalRootStages
