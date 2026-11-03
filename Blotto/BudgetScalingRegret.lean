import Blotto.BudgetScaling

/-! A common positive change of units preserves independent expected payoff,
actual security suprema and both continuous regrets. -/

namespace Blotto
open MeasureTheory

theorem scaleAllocation_inverse_right {n : ℕ} {c : ℝ} (hc : c ≠ 0) (x : Allocation n) :
    scaleAllocation c (scaleAllocation c⁻¹ x) = x := by
  funext j
  simp [scaleAllocation, hc]

theorem scaleLaw_fullBudget {n : ℕ} {c B : ℝ} (hc : 0 ≤ c) (μ : Mixed n)
    (hμ : ∀ᵐ x ∂(μ : Measure (Allocation n)), FullBudget B x) :
    ∀ᵐ x ∂(scaleLaw c μ : Measure (Allocation n)), FullBudget (c * B) x := by
  change ∀ᵐ x ∂Measure.map (scaleAllocation c) (μ : Measure (Allocation n)), FullBudget (c * B) x
  rw [ae_map_iff (measurable_scaleAllocation c).aemeasurable (measurable_fullBudget _)]
  exact hμ.mono (fun _ hx => scaleAllocation_fullBudget hc hx)

theorem purePayoff_scale {n : ℕ} (v : Values n) {c : ℝ} (hc : 0 < c) (x : Allocation n) (ν : Mixed n) :
    purePayoff v (scaleAllocation c x) (scaleLaw c ν) = purePayoff v x ν := by
  unfold purePayoff
  change (∫ y, payoff v (scaleAllocation c x) y ∂Measure.map (scaleAllocation c) (ν : Measure (Allocation n))) = _
  rw [integral_map (measurable_scaleAllocation c).aemeasurable
    (integrable_payoff_right v (scaleAllocation c x) (scaleLaw c ν)).aestronglyMeasurable]
  simp_rw [payoff_scale v hc]

theorem expected_scale {n : ℕ} (v : Values n) {c : ℝ} (hc : 0 < c) (μ ν : Mixed n) :
    expected v (scaleLaw c μ) (scaleLaw c ν) = expected v μ ν := by
  rw [expected_iterated, expected_iterated]
  change (∫ x, purePayoff v x (scaleLaw c ν) ∂Measure.map (scaleAllocation c) (μ : Measure (Allocation n))) = _
  rw [integral_map (measurable_scaleAllocation c).aemeasurable
    (integrable_purePayoff v (scaleLaw c μ) (scaleLaw c ν)).aestronglyMeasurable]
  simp_rw [purePayoff_scale v hc]

theorem security_scale {n : ℕ} (v : Values n) {c : ℝ} (hc : 0 < c) (B : ℝ) (ν : Mixed n) :
    security v (c * B) (scaleLaw c ν) = security v B ν := by
  unfold security
  congr 1
  ext z
  constructor
  · rintro ⟨x, hx, hz⟩
    let y := scaleAllocation c⁻¹ x
    have he : scaleAllocation c y = x := scaleAllocation_inverse_right (ne_of_gt hc) x
    have hy : Feasible B y := (scaleAllocation_feasible_iff hc y).mp (by rw [he]; exact hx)
    refine ⟨y, hy, ?_⟩
    change purePayoff v y ν = z
    rw [← purePayoff_scale v hc y ν, he]
    exact hz
  · rintro ⟨x, hx, hz⟩
    refine ⟨scaleAllocation c x, scaleAllocation_feasible (le_of_lt hc) hx, ?_⟩
    change purePayoff v (scaleAllocation c x) (scaleLaw c ν) = z
    rw [purePayoff_scale v hc]
    exact hz

theorem regret_scale {n : ℕ} (v : Values n) {c : ℝ} (hc : 0 < c) (B : ℝ) (μ ν : Mixed n) :
    regret v (c * B) (scaleLaw c μ) (scaleLaw c ν) = regret v B μ ν := by
  unfold regret
  rw [security_scale v hc, expected_scale v hc]

end Blotto
