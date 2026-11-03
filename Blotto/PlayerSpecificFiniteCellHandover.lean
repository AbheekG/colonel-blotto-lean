import Blotto.PlayerSpecificFiniteScaleContract

/-! The cell caller really copies its returned optional representation.
The source price can therefore be reused as a conservative bound when a
later recognition frame copies that same accepted record. -/
namespace Blotto.PlayerSpecificFiniteCellHandover
open PlayerSpecificRationalCells PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 1500000

theorem returned_copy_le (model : RationalCostModel) (c : Cell) (b : ℚ) :
    price model (PlayerSpecificCandidateScanExecution.copyOption (PlayerSpecificFiniteCellExecution.run model c b).1)≤
      (PlayerSpecificFiniteCellExecution.run model c b).2 := by
  simp only [PlayerSpecificFiniteCellExecution.run]
  split <;> simp only [PlayerSpecificFiniteCellExecution.frame,price_append] <;> omega

end Blotto.PlayerSpecificFiniteCellHandover
