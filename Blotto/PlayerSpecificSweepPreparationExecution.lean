import Blotto.PlayerSpecificCellConstructionCost

/-! Actual one-time rational sweep preparation from the sorted field row:
initial sums, cached suffix maxima and all interval cells. Every caller
input, cached state/suffix and returned cell list is copied and priced. -/
namespace Blotto.PlayerSpecificSweepPreparationExecution
open PlayerSpecificDensePolynomial PlayerSpecificRationalCells PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 1500000

def frame (fields : List (ℚ×ℚ)) (state : PlayerSpecificSweep.State ℚ)
    (suffix : ℚ×PlayerSpecificSuffixExecution.Rows) (cells : List Cell) : Trace :=
  PlayerSpecificSweepExecution.copyFields fields++PlayerSpecificSweepExecution.copyState state++
    copyRow [suffix.1]++PlayerSpecificSuffixExecution.copyRows suffix.2++
    PlayerSpecificRecognitionScanExecution.copyCells cells++[.control fields.length,.control cells.length]
def run (model : RationalCostModel) (fields : List (ℚ×ℚ)) : List Cell×ℕ :=
  let state:=PlayerSpecificSweepExecution.initial fields
  let suffix:=PlayerSpecificSuffixExecution.run fields
  let cells:=PlayerSpecificCellConstructionExecution.run model state.1 0 suffix.1.2
  (cells.1,price model state.2+price model suffix.2+cells.2+price model (frame fields state.1 suffix.1 cells.1))

theorem value (model : RationalCostModel) (fields : List (ℚ×ℚ)) :
    (run model fields).1=build (PlayerSpecificSweep.initial fields) 0 (PlayerSpecificSweepBounds.suffixes fields).2.1 := by
  simp only [run,PlayerSpecificCellConstructionExecution.value,PlayerSpecificSweepExecution.initial_value,
    (PlayerSpecificSuffixExecution.values fields).2]

theorem count (model : RationalCostModel) (fields : List (ℚ×ℚ)) : (run model fields).1.length=fields.length+1 := by
  rw [value,PlayerSpecificRationalCells.count]
  have h:=PlayerSpecificSuffixExecution.rows_length fields
  rw [(PlayerSpecificSuffixExecution.values fields).2] at h
  omega

end Blotto.PlayerSpecificSweepPreparationExecution
