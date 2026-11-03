import Blotto.GeneralPaperCircleSuccessArc

/-! Both CDF conventions of the actual circle minimum change by at most
1/S under the paper's selected midpoint cells. Empty/full events, repeated
cells, zero atoms and equal representative bids are all included. -/
namespace Blotto.GeneralPaperSelectedBidCDF
open GeneralPaperCircleCell GeneralPaperCircleFiniteAverage GeneralPaperSelectedShift
open GeneralPaperCircleThresholdRank
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 1200000

theorem indicator_congr (p q : Prop) [Decidable p] [Decidable q] (h : p↔q) :
    (if p then (1:ℝ) else 0)=(if q then (1:ℝ) else 0) := by
  by_cases hp:p
  · rw [ite_eq_left hp,ite_eq_left (h.mp hp)]
  · rw [ite_eq_right hp,ite_eq_right (fun hq => hp (h.mpr hq))]

theorem event_error (R W S : ℕ) (hR : 0<R) (hW : 0<W) (hS : 0<S) (L f offset : ℕ)
    (hL : L≤R*W) (hf : f≤R) :
    -(1/(S:ℝ))≤average (fun l:Fin S => if
        (choice R W hR hW (cell (R*W) (Nat.mul_pos hR hW) offset (selected (R*W) S (Nat.mul_pos hR hW) hS l).val) L).val<f
        then (1:ℝ) else 0)-average (fun c:Fin (R*W) => if
        (choice R W hR hW (cell (R*W) (Nat.mul_pos hR hW) offset c.val) L).val<f then (1:ℝ) else 0) ∧
      average (fun l:Fin S => if
        (choice R W hR hW (cell (R*W) (Nat.mul_pos hR hW) offset (selected (R*W) S (Nat.mul_pos hR hW) hS l).val) L).val<f
        then (1:ℝ) else 0)-average (fun c:Fin (R*W) => if
        (choice R W hR hW (cell (R*W) (Nat.mul_pos hR hW) offset c.val) L).val<f then (1:ℝ) else 0)≤1/(S:ℝ) := by
  obtain ⟨start,length,hLength,hEvent⟩ := GeneralPaperCircleSuccessArc.event_arc R W hR hW L f hL hf
  have he (c:Fin (R*W)) := indicator_congr _ _ (hEvent (cell (R*W) (Nat.mul_pos hR hW) offset c.val))
  simp_rw [he]
  exact GeneralPaperSelectedArcDiscrepancy.rotated_error (R*W) S (Nat.mul_pos hR hW) hS start length hLength offset

noncomputable def point (R W : ℕ) (hR : 0<R) (hW : 0<W) (L offset : ℕ) (x : Fin R → ℝ) (c : Fin (R*W)) : ℝ :=
  x (choice R W hR hW (cell (R*W) (Nat.mul_pos hR hW) offset c.val) L)

theorem strict_error (R W S : ℕ) (hR : 0<R) (hW : 0<W) (hS : 0<S) (L offset : ℕ) (hL : L≤R*W)
    (x : Fin R → ℝ) (hx : Monotone x) (t : ℝ) :
    -(1/(S:ℝ))≤average (fun l:Fin S => if point R W hR hW L offset x
        (selected (R*W) S (Nat.mul_pos hR hW) hS l)<t then (1:ℝ) else 0)-
      average (fun c:Fin (R*W) => if point R W hR hW L offset x c<t then (1:ℝ) else 0) ∧
      average (fun l:Fin S => if point R W hR hW L offset x
        (selected (R*W) S (Nat.mul_pos hR hW) hS l)<t then (1:ℝ) else 0)-
      average (fun c:Fin (R*W) => if point R W hR hW L offset x c<t then (1:ℝ) else 0)≤1/(S:ℝ) := by
  have he (c:Fin (R*W)) := indicator_congr _ _ (strict_iff x hx t
    (choice R W hR hW (cell (R*W) (Nat.mul_pos hR hW) offset c.val) L))
  unfold point
  simp_rw [he]
  exact event_error R W S hR hW hS L (strict x t) offset hL (strict_le x t)

theorem weak_error (R W S : ℕ) (hR : 0<R) (hW : 0<W) (hS : 0<S) (L offset : ℕ) (hL : L≤R*W)
    (x : Fin R → ℝ) (hx : Monotone x) (t : ℝ) :
    -(1/(S:ℝ))≤average (fun l:Fin S => if point R W hR hW L offset x
        (selected (R*W) S (Nat.mul_pos hR hW) hS l)≤t then (1:ℝ) else 0)-
      average (fun c:Fin (R*W) => if point R W hR hW L offset x c≤t then (1:ℝ) else 0) ∧
      average (fun l:Fin S => if point R W hR hW L offset x
        (selected (R*W) S (Nat.mul_pos hR hW) hS l)≤t then (1:ℝ) else 0)-
      average (fun c:Fin (R*W) => if point R W hR hW L offset x c≤t then (1:ℝ) else 0)≤1/(S:ℝ) := by
  have he (c:Fin (R*W)) := indicator_congr _ _ (weak_iff x hx t
    (choice R W hR hW (cell (R*W) (Nat.mul_pos hR hW) offset c.val) L))
  unfold point
  simp_rw [he]
  exact event_error R W S hR hW hS L (weak x t) offset hL (weak_le x t)

theorem share_error (R W S : ℕ) (hR : 0<R) (hW : 0<W) (hS : 0<S) (L offset : ℕ) (hL : L≤R*W)
    (x : Fin R → ℝ) (hx : Monotone x) (y : ℝ) :
    -(1/(S:ℝ))≤average (fun l:Fin S => share y (point R W hR hW L offset x
        (selected (R*W) S (Nat.mul_pos hR hW) hS l)))-
      average (fun c:Fin (R*W) => share y (point R W hR hW L offset x c)) ∧
      average (fun l:Fin S => share y (point R W hR hW L offset x
        (selected (R*W) S (Nat.mul_pos hR hW) hS l)))-
      average (fun c:Fin (R*W) => share y (point R W hR hW L offset x c))≤1/(S:ℝ) := by
  have hs := strict_error R W S hR hW hS L offset hL x hx y
  have hw := weak_error R W S hR hW hS L offset hL x hx y
  simp_rw [half_indicator,average_div,average_add]
  constructor <;> linarith only [hs.1,hs.2,hw.1,hw.2]

end Blotto.GeneralPaperSelectedBidCDF
