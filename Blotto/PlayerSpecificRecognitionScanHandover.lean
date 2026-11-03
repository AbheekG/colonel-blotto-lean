import Blotto.PlayerSpecificRationalIntervalsContract

/-! Every actual recognition scan frame copies its returned selected
cell/root. This source inequality transports the complete record-copy cost
to the final parameter/description caller without a representation oracle. -/
namespace Blotto.PlayerSpecificRecognitionScanHandover
open PlayerSpecificRationalCells PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 1500000

theorem returned_copy_le (model : RationalCostModel) (b : ℚ) (cells : List Cell) :
    price model (PlayerSpecificRecognitionScanExecution.copyResult (PlayerSpecificRecognitionScanExecution.run model b cells).1)≤
      (PlayerSpecificRecognitionScanExecution.run model b cells).2 := by
  cases cells with
  | nil =>
    simp only [PlayerSpecificRecognitionScanExecution.run,PlayerSpecificRecognitionScanExecution.frame,price_append]
    omega
  | cons c cs =>
    simp only [PlayerSpecificRecognitionScanExecution.run]
    split <;> simp only [PlayerSpecificRecognitionScanExecution.frame,price_append] <;> omega

end Blotto.PlayerSpecificRecognitionScanHandover
