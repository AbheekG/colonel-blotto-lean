import Blotto.UpperEventCDF
import Mathlib.MeasureTheory.Integral.Layercake

/-! A bounded monotone observable changes in expectation by at most the
Kolmogorov distance. The layer-cake proof uses actual tail probabilities,
including both possible boundary conventions for a real upper event. -/

namespace Blotto
open MeasureTheory Set Filter

theorem integrable_unit_observable (ρ : ProbabilityMeasure ℝ) (f : ℝ → ℝ) (hf : Measurable f)
    (hbound : ∀ x, 0 ≤ f x ∧ f x ≤ 1) : Integrable f (ρ : Measure ℝ) := by
  apply (integrable_const (1 : ℝ)).mono' hf.aestronglyMeasurable
  exact Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs, abs_of_nonneg (hbound x).1] using (hbound x).2)

namespace RealCDFClose

theorem monotone_integral {ρ σ : ProbabilityMeasure ℝ} {δ : ℝ} (h : RealCDFClose ρ σ δ)
    (f : ℝ → ℝ) (hf : Monotone f) (hbound : ∀ x, 0 ≤ f x ∧ f x ≤ 1) :
    |(∫ x, f x ∂(ρ : Measure ℝ)) - (∫ x, f x ∂(σ : Measure ℝ))| ≤ δ := by
  have hρ := integrable_unit_observable ρ f hf.measurable hbound
  have hσ := integrable_unit_observable σ f hf.measurable hbound
  have hnρ : 0 ≤ᵐ[(ρ : Measure ℝ)] f := Eventually.of_forall (fun x => (hbound x).1)
  have hnσ : 0 ≤ᵐ[(σ : Measure ℝ)] f := Eventually.of_forall (fun x => (hbound x).1)
  have hbρ : f ≤ᵐ[(ρ : Measure ℝ)] (fun _ => 1) := Eventually.of_forall (fun x => (hbound x).2)
  have hbσ : f ≤ᵐ[(σ : Measure ℝ)] (fun _ => 1) := Eventually.of_forall (fun x => (hbound x).2)
  let ν : Measure ℝ := volume.restrict (Ioc 0 1)
  let : IsFiniteMeasure ν := ⟨by simp [ν]⟩
  have htρ : Measurable (fun y => (ρ : Measure ℝ).real {x | y ≤ f x}) := by
    apply Measurable.ennreal_toReal
    exact Antitone.measurable (fun y z hyz => measure_mono (fun x hx => hyz.trans hx))
  have htσ : Measurable (fun y => (σ : Measure ℝ).real {x | y ≤ f x}) := by
    apply Measurable.ennreal_toReal
    exact Antitone.measurable (fun y z hyz => measure_mono (fun x hx => hyz.trans hx))
  have hiρ : Integrable (fun y => (ρ : Measure ℝ).real {x | y ≤ f x}) ν := by
    apply (integrable_const (1 : ℝ)).mono' htρ.aestronglyMeasurable
    exact Eventually.of_forall (fun y => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg] using (measureReal_le_one (μ := (ρ : Measure ℝ)) (s := {x | y ≤ f x})))
  have hiσ : Integrable (fun y => (σ : Measure ℝ).real {x | y ≤ f x}) ν := by
    apply (integrable_const (1 : ℝ)).mono' htσ.aestronglyMeasurable
    exact Eventually.of_forall (fun y => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg] using (measureReal_le_one (μ := (σ : Measure ℝ)) (s := {x | y ≤ f x})))
  rw [hρ.integral_eq_integral_Ioc_meas_le hnρ hbρ, hσ.integral_eq_integral_Ioc_meas_le hnσ hbσ]
  change |(∫ y, (ρ : Measure ℝ).real {x | y ≤ f x} ∂ν) -
    (∫ y, (σ : Measure ℝ).real {x | y ≤ f x} ∂ν)| ≤ δ
  rw [← integral_sub hiρ hiσ]
  have he := norm_integral_le_of_norm_le_const (μ := ν) (C := δ)
    (Eventually.of_forall (fun y => by
      rw [Real.norm_eq_abs]
      exact h.upper_event {x | y ≤ f x} (fun x hx z hxz => hx.trans (hf hxz))))
  simpa [ν, Real.norm_eq_abs, measureReal_def, Real.volume_Ioc] using he

theorem difference_integral {ρ σ : ProbabilityMeasure ℝ} {δ : ℝ} (h : RealCDFClose ρ σ δ)
    (f g k : ℝ → ℝ) (hg : Monotone g) (hk : Monotone k)
    (hgb : ∀ x, 0 ≤ g x ∧ g x ≤ 1) (hkb : ∀ x, 0 ≤ k x ∧ k x ≤ 1)
    (hρ : f =ᵐ[(ρ : Measure ℝ)] (fun x => g x - k x))
    (hσ : f =ᵐ[(σ : Measure ℝ)] (fun x => g x - k x)) :
    |(∫ x, f x ∂(ρ : Measure ℝ)) - (∫ x, f x ∂(σ : Measure ℝ))| ≤ 2 * δ := by
  rw [integral_congr_ae hρ, integral_congr_ae hσ,
    integral_sub (integrable_unit_observable ρ g hg.measurable hgb) (integrable_unit_observable ρ k hk.measurable hkb),
    integral_sub (integrable_unit_observable σ g hg.measurable hgb) (integrable_unit_observable σ k hk.measurable hkb)]
  have heG := abs_le.mp (h.monotone_integral g hg hgb)
  have heK := abs_le.mp (h.monotone_integral k hk hkb)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end RealCDFClose
end Blotto
