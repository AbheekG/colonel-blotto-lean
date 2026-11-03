import Blotto.Mixed
import Blotto.SegmentLottery

/-! Positive common budget scaling preserves every tie and the full
continuous at-most deviation domain. No maximizer is assumed. -/

namespace Blotto
open MeasureTheory
open scoped BigOperators

noncomputable def scaleAllocation {n : ℕ} (c : ℝ) (x : Allocation n) : Allocation n := fun j => c * x j

theorem measurable_scaleAllocation {n : ℕ} (c : ℝ) : Measurable (scaleAllocation (n := n) c) := by
  apply Measurable.of_eval
  intro j
  exact measurable_const.mul (measurable_pi_apply j)

theorem scaleAllocation_fullBudget {n : ℕ} {c B : ℝ} (hc : 0 ≤ c) {x : Allocation n}
    (hx : FullBudget B x) : FullBudget (c * B) (scaleAllocation c x) := by
  constructor
  · exact fun j => mul_nonneg hc (hx.1 j)
  · simp only [scaleAllocation, ← Finset.mul_sum, hx.2]

theorem scaleAllocation_feasible {n : ℕ} {c B : ℝ} (hc : 0 ≤ c) {x : Allocation n}
    (hx : Feasible B x) : Feasible (c * B) (scaleAllocation c x) := by
  constructor
  · exact fun j => mul_nonneg hc (hx.1 j)
  · simp only [scaleAllocation, ← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hx.2 hc

theorem scaleAllocation_inverse {n : ℕ} {c : ℝ} (hc : c ≠ 0) (x : Allocation n) :
    scaleAllocation c⁻¹ (scaleAllocation c x) = x := by
  funext j
  simp [scaleAllocation, hc]

theorem scaleAllocation_feasible_iff {n : ℕ} {c B : ℝ} (hc : 0 < c) (x : Allocation n) :
    Feasible (c * B) (scaleAllocation c x) ↔ Feasible B x := by
  constructor
  · intro h
    have he := scaleAllocation_feasible (le_of_lt (inv_pos.mpr hc)) h
    rw [scaleAllocation_inverse (ne_of_gt hc)] at he
    simpa only [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hc), one_mul] using he
  · exact scaleAllocation_feasible (le_of_lt hc)

theorem share_scale {c : ℝ} (hc : 0 < c) (s t : ℝ) : share (c * s) (c * t) = share s t := by
  simp only [share, mul_lt_mul_iff_of_pos_left hc, mul_right_inj' (ne_of_gt hc)]

theorem payoff_scale {n : ℕ} (v : Values n) {c : ℝ} (hc : 0 < c) (x y : Allocation n) :
    payoff v (scaleAllocation c x) (scaleAllocation c y) = payoff v x y := by
  simp only [payoff, scaleAllocation, share_scale hc]

noncomputable def scaleLaw {n : ℕ} (c : ℝ) (μ : Mixed n) : Mixed n := μ.map (scaleAllocation c)

theorem measurable_feasible {n : ℕ} (B : ℝ) : MeasurableSet {x : Allocation n | Feasible B x} := by
  have hn : MeasurableSet {x : Allocation n | ∀ j, 0 ≤ x j} := by
    have he : {x : Allocation n | ∀ j, 0 ≤ x j} = ⋂ j : Fin n, {x | 0 ≤ x j} := by
      ext x
      simp
    rw [he]
    exact MeasurableSet.iInter fun j : Fin n =>
      measurableSet_le (measurable_const : Measurable (fun _ : Allocation n => (0 : ℝ))) (measurable_pi_apply j)
  have hs : Measurable (fun x : Allocation n => ∑ j, x j) :=
    Finset.measurable_sum _ (fun j _ => measurable_pi_apply j)
  exact hn.inter (measurableSet_le hs measurable_const)

theorem scaleLaw_supported {n : ℕ} {c B : ℝ} (hc : 0 ≤ c) (μ : Mixed n) (hμ : Supported B μ) :
    Supported (c * B) (scaleLaw c μ) := by
  change ∀ᵐ x ∂Measure.map (scaleAllocation c) (μ : Measure (Allocation n)), Feasible (c * B) x
  rw [ae_map_iff (measurable_scaleAllocation c).aemeasurable (measurable_feasible _)]
  exact hμ.mono (fun _ hx => scaleAllocation_feasible hc hx)

end Blotto
