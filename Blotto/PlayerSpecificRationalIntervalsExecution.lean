import Blotto.PlayerSpecificSortedFieldsContract

/-! Complete finite-bit rational interval preparation, from original input
through native stable sorting and one-time sweep construction. All cached
field rows, original input and returned cell records are priced. -/
namespace Blotto.PlayerSpecificRationalIntervalsExecution
open PlayerSpecificRationalCells PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 1500000

def frame {N : ℕ} (i : RationalPlayerSpecificInput N) (fields : List (ℚ×ℚ)) (cells : List Cell) : Trace :=
  copyRow (PlayerSpecificRecognitionInputHeights.row i)++PlayerSpecificSweepExecution.copyFields fields++
    PlayerSpecificRecognitionScanExecution.copyCells cells++[.control N,.control cells.length]
def run {N : ℕ} (model : RationalCostModel) (i : RationalPlayerSpecificInput N) : List Cell×ℕ :=
  let fields:=PlayerSpecificSortedFieldsExecution.run model i
  let cells:=PlayerSpecificSweepPreparationExecution.run model fields.1
  (cells.1,fields.2+cells.2+price model (frame i fields.1 cells.1))

theorem value {N : ℕ} (model : RationalCostModel) (i : RationalPlayerSpecificInput N) :
    (run model i).1=PlayerSpecificRationalIntervals.run i := by
  simp only [run,PlayerSpecificSweepPreparationExecution.value,PlayerSpecificSortedFieldsExecution.value,
    PlayerSpecificRationalIntervals.run]

theorem length {N : ℕ} (model : RationalCostModel) (i : RationalPlayerSpecificInput N) : (run model i).1.length=N+1 := by
  rw [value,PlayerSpecificRationalIntervals.count]

theorem heights {N : ℕ} (model : RationalCostModel) (i : RationalPlayerSpecificInput N) :
    ∀ c∈(run model i).1,PlayerSpecificRationalCellHeights.CellHeight c
      (PlayerSpecificRecognitionInputHeights.cellHeight N (PlayerSpecificRecognitionInputHeights.inputHeight i)) := by
  rw [value]
  exact PlayerSpecificRecognitionInputHeights.cells i

end Blotto.PlayerSpecificRationalIntervalsExecution
