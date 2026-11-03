import Blotto.GeneralPaperCircleFiniteAverage

/-! Actual strict/weak bid CDFs and canonical half-tie payoff of one
finite-cell arc minimum. Equal bids, zero atoms and empty/full threshold
sets are covered by the same bound. -/
namespace Blotto.GeneralPaperCircleBidCDF
open GeneralPaperCircleCell GeneralPaperCircleThresholdRank GeneralPaperCircleFiniteAverage
open MeasureTheory
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 900000

noncomputable def point (R W : ℕ) (hR : 0<R) (hW : 0<W) (w : ℕ) (x : Fin R → ℝ) : Fin (R*W) → ℝ :=
  fun c => x (choice R W hR hW c (R*w))

theorem choice_le_bin (R W : ℕ) (hR : 0<R) (hW : 0<W) (L : ℕ) (c : Fin (R*W)) :
    choice R W hR hW c L≤bin R W hW c := by
  unfold choice
  split_ifs
  · exact Nat.zero_le _
  · exact le_rfl

theorem indicator_imp (p q : Prop) [Decidable p] [Decidable q] (h : p → q) :
    (if p then (1:ℝ) else 0)≤(if q then 1 else 0) := by
  by_cases hp : p
  · simp only [ite_eq_left hp,ite_eq_left (h hp),le_refl]
  · simp only [ite_eq_right hp]
    split_ifs <;> norm_num

theorem strict_upper (R W : ℕ) (hR : 0<R) (hW : 0<W) (w : ℕ) (x : Fin R → ℝ) (hx : Monotone x) (t : ℝ) :
    (strict (point R W hR hW w x) t:ℝ)/(R*W:ℕ)≤(strict x t:ℝ)/R+(w:ℝ)/W := by
  change ((Finset.univ.filter (fun c:Fin (R*W) => x (choice R W hR hW c (R*w))<t)).card:ℝ)/(R*W:ℕ)≤_
  rw [strict_event R W hR hW (R*w) x hx t]
  exact GeneralPaperCircleCDFCount.probability_bound R W hR hW w (strict x t)

theorem weak_upper (R W : ℕ) (hR : 0<R) (hW : 0<W) (w : ℕ) (x : Fin R → ℝ) (hx : Monotone x) (t : ℝ) :
    (weak (point R W hR hW w x) t:ℝ)/(R*W:ℕ)≤(weak x t:ℝ)/R+(w:ℝ)/W := by
  change ((Finset.univ.filter (fun c:Fin (R*W) => x (choice R W hR hW c (R*w))≤t)).card:ℝ)/(R*W:ℕ)≤_
  rw [weak_event R W hR hW (R*w) x hx t]
  exact GeneralPaperCircleCDFCount.probability_bound R W hR hW w (weak x t)

theorem strict_lower (R W : ℕ) (hR : 0<R) (hW : 0<W) (w : ℕ) (x : Fin R → ℝ) (hx : Monotone x) (t : ℝ) :
    (strict x t:ℝ)/R≤(strict (point R W hR hW w x) t:ℝ)/(R*W:ℕ) := by
  have h := average_le (fun c:Fin (R*W) => if x (bin R W hW c)<t then (1:ℝ) else 0)
    (fun c => if point R W hR hW w x c<t then 1 else 0) (fun c =>
      indicator_imp _ _ (fun hc => (hx (choice_le_bin R W hR hW (R*w) c)).trans_lt hc))
  rw [average_bins R W hR hW (fun a => if x a<t then (1:ℝ) else 0),average_indicator,average_indicator] at h
  exact h

theorem weak_lower (R W : ℕ) (hR : 0<R) (hW : 0<W) (w : ℕ) (x : Fin R → ℝ) (hx : Monotone x) (t : ℝ) :
    (weak x t:ℝ)/R≤(weak (point R W hR hW w x) t:ℝ)/(R*W:ℕ) := by
  have h := average_le (fun c:Fin (R*W) => if x (bin R W hW c)≤t then (1:ℝ) else 0)
    (fun c => if point R W hR hW w x c≤t then 1 else 0) (fun c =>
      indicator_imp _ _ (fun hc => (hx (choice_le_bin R W hR hW (R*w) c)).trans hc))
  rw [average_bins R W hR hW (fun a => if x a≤t then (1:ℝ) else 0),average_indicator,average_indicator] at h
  exact h

theorem strict_error (R W : ℕ) (hR : 0<R) (hW : 0<W) (w : ℕ) (x : Fin R → ℝ) (hx : Monotone x) (t : ℝ) :
    0≤(strict (point R W hR hW w x) t:ℝ)/(R*W:ℕ)-(strict x t:ℝ)/R ∧
      (strict (point R W hR hW w x) t:ℝ)/(R*W:ℕ)-(strict x t:ℝ)/R≤(w:ℝ)/W := by
  have hl := strict_lower R W hR hW w x hx t
  have hu := strict_upper R W hR hW w x hx t
  constructor <;> linarith only [hl,hu]

theorem weak_error (R W : ℕ) (hR : 0<R) (hW : 0<W) (w : ℕ) (x : Fin R → ℝ) (hx : Monotone x) (t : ℝ) :
    0≤(weak (point R W hR hW w x) t:ℝ)/(R*W:ℕ)-(weak x t:ℝ)/R ∧
      (weak (point R W hR hW w x) t:ℝ)/(R*W:ℕ)-(weak x t:ℝ)/R≤(w:ℝ)/W := by
  have hl := weak_lower R W hR hW w x hx t
  have hu := weak_upper R W hR hW w x hx t
  constructor <;> linarith only [hl,hu]

theorem law_cdf_close (R W : ℕ) (hR : 0<R) (hW : 0<W) (w : ℕ) (x : Fin R → ℝ) (hx : Monotone x) :
    RealCDFClose (finiteUniformPoints hR x)
      (finiteUniformPoints (Nat.mul_pos hR hW) (point R W hR hW w x)) ((w:ℝ)/W) := by
  intro t
  rw [law_weak,law_weak]
  have h := weak_error R W hR hW w x hx t
  apply abs_le.mpr
  constructor <;> linarith only [h.1,h.2]

theorem share_error (R W : ℕ) (hR : 0<R) (hW : 0<W) (w : ℕ) (x : Fin R → ℝ) (hx : Monotone x) (y : ℝ) :
    0≤average (fun c => share y (point R W hR hW w x c))-average (fun a => share y (x a)) ∧
      average (fun c => share y (point R W hR hW w x c))-average (fun a => share y (x a))≤(w:ℝ)/W := by
  rw [average_share,average_share]
  have hs := strict_error R W hR hW w x hx y
  have hw := weak_error R W hR hW w x hx y
  constructor <;> linarith only [hs.1,hs.2,hw.1,hw.2]

end Blotto.GeneralPaperCircleBidCDF
