import Blotto.GeneralPaperCircleBidCDF

/-! Actual scaled arc bids under one common whole-row shift. A battlefield's
prefix offset merely permutes the uniform cells; no independent coordinate
shifts are introduced. Every real opposing bid, including zero ties, is covered. -/
namespace Blotto.GeneralPaperCircleCoordinatePayoff
open GeneralPaperCircleCell GeneralPaperCircleFiniteAverage
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 900000

noncomputable def coefficient (R W w : ℕ) : ℝ := ((R*w:ℕ):ℝ)/W

theorem coefficient_nonnegative (R W w : ℕ) : 0≤coefficient R W w :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

noncomputable def curve (R W : ℕ) (hR : 0<R) (hW : 0<W) (w offset : ℕ) (x : Fin R → ℝ) : Fin (R*W) → ℝ :=
  fun s => GeneralPaperCircleBidCDF.point R W hR hW w (fun a => coefficient R W w*x a)
    (cell (R*W) (Nat.mul_pos hR hW) s.val offset)

theorem curve_average (R W : ℕ) (hR : 0<R) (hW : 0<W) (w offset : ℕ) (x : Fin R → ℝ) (f : ℝ → ℝ) :
    average (fun s => f (curve R W hR hW w offset x s))=
      average (fun c => f (GeneralPaperCircleBidCDF.point R W hR hW w (fun a => coefficient R W w*x a) c)) := by
  have he : ∀ s:Fin (R*W),cell (R*W) (Nat.mul_pos hR hW) s.val offset=
      cell (R*W) (Nat.mul_pos hR hW) offset s.val := by
    intro s
    apply Fin.ext
    exact congrArg (fun t => t%(R*W)) (Nat.add_comm s.val offset)
  unfold curve
  simp_rw [he]
  exact average_rotation (R*W) (Nat.mul_pos hR hW) offset
    (fun c => f (GeneralPaperCircleBidCDF.point R W hR hW w (fun a => coefficient R W w*x a) c))

theorem bid_average {g : ℕ} (R W : ℕ) (hR : 0<R) (hW : 0<W) (weights : Fin g → ℕ)
    (x : Fin R → ℝ) (y : ℝ) (j : Fin g) :
    average (fun s:Fin (R*W) => share y (GeneralPaperCircleHardBudget.bid R W hR hW weights x s.val j))=
      average (fun c => share y (GeneralPaperCircleBidCDF.point R W hR hW (weights j)
        (fun a => coefficient R W (weights j)*x a) c)) := by
  change average (fun s => share y (curve R W hR hW (weights j)
    (GeneralPaperCircleArcPartition.before (GeneralPaperCircleHardBudget.lengths R weights) j.val) x s))=_
  exact curve_average R W hR hW (weights j) _ x (fun t => share y t)

theorem bid_error {g : ℕ} (R W : ℕ) (hR : 0<R) (hW : 0<W) (weights : Fin g → ℕ)
    (x : Fin R → ℝ) (hx : Monotone x) (y : ℝ) (j : Fin g) :
    0≤average (fun s:Fin (R*W) => share y (GeneralPaperCircleHardBudget.bid R W hR hW weights x s.val j))-
        average (fun a => share y (coefficient R W (weights j)*x a)) ∧
      average (fun s:Fin (R*W) => share y (GeneralPaperCircleHardBudget.bid R W hR hW weights x s.val j))-
        average (fun a => share y (coefficient R W (weights j)*x a))≤(weights j:ℝ)/W := by
  have h := GeneralPaperCircleBidCDF.share_error R W hR hW (weights j)
    (fun a => coefficient R W (weights j)*x a)
    (fun _ _ hab => mul_le_mul_of_nonneg_left (hx hab) (coefficient_nonnegative R W (weights j))) y
  simpa only [bid_average] using h

end Blotto.GeneralPaperCircleCoordinatePayoff
