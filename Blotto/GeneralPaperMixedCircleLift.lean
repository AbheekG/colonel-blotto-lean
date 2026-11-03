import Blotto.GeneralPaperCircleMeasurability

/-! Arbitrary whole-row distributions in the full-cell circle lift. No
finite-support, symmetry, or coordinate-independence hypothesis is used.
The continuous-rotation representation is a separate geometric join. -/
namespace Blotto.GeneralPaperMixedCircleLift
open MeasureTheory
open scoped BigOperators
open GeneralPaperCircleFiniteAverage GeneralPaperCircleCanonicalLift
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

noncomputable def law {h g : ℕ} (R W : ℕ) (hR : 0 < R) (hW : 0 < W)
    (weights : Fin g → ℕ) (P : Mixed (h+R)) : Mixed (h+g) :=
  GeneralPaperUniformRowLaw.mixture (Nat.mul_pos hR hW)
    (fun s : Fin (R*W) => P.map (fun x => row R W hR hW weights x s.val))

theorem supported {h g : ℕ} (R W : ℕ) (hR : 0 < R) (hW : 0 < W)
    (weights : Fin g → ℕ) (hs : ∑ j, weights j = W)
    (P : Mixed (h+R)) (B : ℝ) (hP : Supported B P) :
    Supported B (law R W hR hW weights P) := by
  apply GeneralPaperUniformRowLaw.mixture_supported
  intro s
  change ∀ᵐ x ∂Measure.map (fun x => row R W hR hW weights x s.val) (P : Measure (Allocation (h+R))), Feasible B x
  rw [ae_map_iff (GeneralPaperCircleMeasurability.row R W hR hW weights s.val).aemeasurable
    (measurable_feasible B)]
  exact hP.mono (fun x hx => row_feasible R W hR hW weights hs x B hx s.val)

theorem integrable_row_payoff {h g : ℕ} (R W : ℕ) (hR : 0 < R) (hW : 0 < W)
    (weights : Fin g → ℕ) (P : Mixed (h+R)) (v : Values (h+g)) (y : Allocation (h+g)) (s : ℕ) :
    Integrable (fun x => payoff v y (row R W hR hW weights x s)) (P : Measure (Allocation (h+R))) :=
  (integrable_payoff_right v y (P.map (fun x => row R W hR hW weights x s))).comp_measurable
    (GeneralPaperCircleMeasurability.row R W hR hW weights s)

theorem integral_average {α : Type*} [MeasurableSpace α] {N : ℕ}
    (μ : Measure α) (f : Fin N → α → ℝ) (hf : ∀ i, Integrable (f i) μ) :
    (∫ x, average (fun i => f i x) ∂μ) = average (fun i => ∫ x, f i x ∂μ) := by
  unfold GeneralPaperCircleFiniteAverage.average
  rw [integral_div, integral_finsetSum _ (fun i _ => hf i)]

theorem integrable_average {α : Type*} [MeasurableSpace α] {N : ℕ}
    (μ : Measure α) (f : Fin N → α → ℝ) (hf : ∀ i, Integrable (f i) μ) :
    Integrable (fun x => average (fun i => f i x)) μ :=
  (integrable_finsetSum _ (fun i _ => hf i)).div_const _

theorem pure_law {h g : ℕ} (R W : ℕ) (hR : 0 < R) (hW : 0 < W)
    (weights : Fin g → ℕ) (P : Mixed (h+R)) (v : Values (h+g)) (y : Allocation (h+g)) :
    purePayoff v y (law R W hR hW weights P) =
      ∫ x, average (fun s : Fin (R*W) => payoff v y (row R W hR hW weights x s.val))
        ∂(P : Measure (Allocation (h+R))) := by
  rw [law, GeneralPaperUniformRowLaw.pure_mixture, integral_average]
  · congr 1
    funext s
    unfold purePayoff
    change (∫ z, payoff v y z ∂Measure.map (fun x => row R W hR hW weights x s.val)
      (P : Measure (Allocation (h+R)))) = _
    exact integral_map (GeneralPaperCircleMeasurability.row R W hR hW weights s.val).aemeasurable
      (integrable_payoff_right v y (P.map (fun x => row R W hR hW weights x s.val))).aestronglyMeasurable
  · exact fun s => integrable_row_payoff R W hR hW weights P v y s.val

theorem pure_bound {h g : ℕ} (R W Q : ℕ) (hR : 0 < R) (hW : 0 < W) (hQ : 0 < Q)
    (weights : Fin g → ℕ) (hp : ∀ j, 0 < weights j) (hs : ∑ j, weights j = W)
    (v : Values (h+g)) (vRed : Values (h+R))
    (hk : ∀ j : Fin h, v.weight (Fin.castAdd g j) = vRed.weight (Fin.castAdd R j))
    (hl : ∀ j : Fin g, v.weight (Fin.natAdd h j) = (weights j : ℝ)/Q)
    (hr : ∀ a : Fin R, vRed.weight (Fin.natAdd h a) = ((W : ℝ)/Q)/R)
    (P : Mixed (h+R)) (B : ℝ) (y : Allocation (h+g)) (hy : Feasible B y) :
    purePayoff v y (law R W hR hW weights P) ≤ security vRed B P +
      GeneralPaperCircleLightPayoff.loss W weights (fun j => (weights j : ℝ)/Q) + ((W : ℝ)/Q)/R := by
  let μ := (P : Measure (Allocation (h+R)))
  let C := GeneralPaperCircleLightPayoff.loss W weights (fun j => (weights j : ℝ)/Q) + ((W : ℝ)/Q)/R
  let reduced := fun (s : Fin R) (x : Allocation (h+R)) => payoff vRed
    (GeneralPaperCyclicQuantileDeviation.row R W hR hW weights hs (kept y) (representatives y) s.val) x
  have hiRed (s : Fin R) : Integrable (reduced s) μ := integrable_payoff_right vRed _ P
  have hiLift := integrable_average μ
    (fun (s : Fin (R*W)) x => payoff v y (row R W hR hW weights x s.val))
    (fun s => integrable_row_payoff R W hR hW weights P v y s.val)
  have hiRight : Integrable (fun x => average (fun s => reduced s x) + C) μ :=
    (integrable_average μ reduced hiRed).add (integrable_const C)
  have hPoint (x : Allocation (h+R)) :
      average (fun s : Fin (R*W) => payoff v y (row R W hR hW weights x s.val)) ≤
        average (fun s : Fin R => reduced s x) + C := by
    have h := payoff_bound R W Q hR hW hQ weights hp hs v vRed hk hl hr
      (kept y) (representatives y) (fun j => hy.1 (Fin.natAdd h j)) x
    simpa only [split_row, C, reduced, add_assoc] using h
  have hIntegral := integral_mono hiLift hiRight hPoint
  rw [integral_add (integrable_average μ reduced hiRed) (integrable_const C),
    integral_average μ reduced hiRed] at hIntegral
  have hConst : (∫ _ : Allocation (h+R), C ∂μ) = C := by simp [μ]
  rw [hConst] at hIntegral
  have hSec : average (fun s : Fin R => ∫ x, reduced s x ∂μ) ≤ security vRed B P := by
    rw [← average_const hR (security vRed B P)]
    apply average_le
    intro s
    apply purePayoff_le_security vRed _ P
    apply GeneralPaperCyclicQuantileDeviation.feasible R W hR hW weights hp hs
    simpa only [split_row] using hy
  rw [pure_law]
  exact hIntegral.trans (by dsimp only [C]; linarith only [hSec])

theorem security_bound {h g : ℕ} (R W Q : ℕ) (hR : 0 < R) (hW : 0 < W) (hQ : 0 < Q)
    (weights : Fin g → ℕ) (hp : ∀ j, 0 < weights j) (hs : ∑ j, weights j = W)
    (v : Values (h+g)) (vRed : Values (h+R))
    (hk : ∀ j : Fin h, v.weight (Fin.castAdd g j) = vRed.weight (Fin.castAdd R j))
    (hl : ∀ j : Fin g, v.weight (Fin.natAdd h j) = (weights j : ℝ)/Q)
    (hr : ∀ a : Fin R, vRed.weight (Fin.natAdd h a) = ((W : ℝ)/Q)/R)
    (P : Mixed (h+R)) (B : ℝ) (hB : 0 ≤ B) :
    security v B (law R W hR hW weights P) ≤ security vRed B P +
      GeneralPaperCircleLightPayoff.loss W weights (fun j => (weights j : ℝ)/Q) + ((W : ℝ)/Q)/R := by
  apply security_le v hB
  intro y hy
  exact pure_bound R W Q hR hW hQ weights hp hs v vRed hk hl hr P B y hy

end Blotto.GeneralPaperMixedCircleLift
