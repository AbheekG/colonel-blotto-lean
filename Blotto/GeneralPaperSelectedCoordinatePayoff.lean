import Blotto.GeneralPaperSelectedBidCDF

/-! Selected-shift half-tie payoff error for each actual scaled arc bid,
with its common-shift prefix offset and the original representative row. -/
namespace Blotto.GeneralPaperSelectedCoordinatePayoff
open GeneralPaperCircleFiniteAverage GeneralPaperSelectedShift
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem bid_point {g : ℕ} (R W : ℕ) (hR : 0<R) (hW : 0<W) (weights : Fin g → ℕ)
    (x : Fin R → ℝ) (j : Fin g) (c : Fin (R*W)) :
    GeneralPaperCircleHardBudget.bid R W hR hW weights x c.val j=
      GeneralPaperSelectedBidCDF.point R W hR hW (R*weights j)
        (GeneralPaperCircleArcPartition.before (GeneralPaperCircleHardBudget.lengths R weights) j.val)
        (fun a => GeneralPaperCircleCoordinatePayoff.coefficient R W (weights j)*x a) c := by
  have he : GeneralPaperCircleCell.cell (R*W) (Nat.mul_pos hR hW) c.val
      (GeneralPaperCircleArcPartition.before (GeneralPaperCircleHardBudget.lengths R weights) j.val)=
    GeneralPaperCircleCell.cell (R*W) (Nat.mul_pos hR hW)
      (GeneralPaperCircleArcPartition.before (GeneralPaperCircleHardBudget.lengths R weights) j.val) c.val := by
    apply Fin.ext
    exact congrArg (fun t => t%(R*W)) (Nat.add_comm _ _)
  unfold GeneralPaperCircleHardBudget.bid GeneralPaperSelectedBidCDF.point
  rw [he]
  rfl

theorem share_error {g : ℕ} (R W S : ℕ) (hR : 0<R) (hW : 0<W) (hS : 0<S)
    (weights : Fin g → ℕ) (x : Fin R → ℝ) (hx : Monotone x) (j : Fin g) (hj : weights j≤W) (y : ℝ) :
    -(1/(S:ℝ))≤average (fun l:Fin S => share y
        (GeneralPaperCircleHardBudget.bid R W hR hW weights x (selected (R*W) S (Nat.mul_pos hR hW) hS l).val j))-
      average (fun c:Fin (R*W) => share y (GeneralPaperCircleHardBudget.bid R W hR hW weights x c.val j)) ∧
      average (fun l:Fin S => share y
        (GeneralPaperCircleHardBudget.bid R W hR hW weights x (selected (R*W) S (Nat.mul_pos hR hW) hS l).val j))-
      average (fun c:Fin (R*W) => share y (GeneralPaperCircleHardBudget.bid R W hR hW weights x c.val j))≤1/(S:ℝ) := by
  simp_rw [bid_point]
  apply GeneralPaperSelectedBidCDF.share_error R W S hR hW hS (R*weights j) _ (Nat.mul_le_mul_left R hj)
  exact fun _ _ hab => mul_le_mul_of_nonneg_left (hx hab) (GeneralPaperCircleCoordinatePayoff.coefficient_nonnegative R W (weights j))

end Blotto.GeneralPaperSelectedCoordinatePayoff
