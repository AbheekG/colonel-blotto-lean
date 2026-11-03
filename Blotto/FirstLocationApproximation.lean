import Blotto.NestedFirst
import Blotto.NestedCDFDecomposition
import Blotto.DyadicLocation

/-! Replacing the first nested case's outer location law has an actual
whole-allocation approximation, exact first two marginals, and third-CDF
error at most twice the location distance. This closes the dependent averaging
estimate rather than inferring it from the scalar location distance alone. -/

namespace Blotto.NestedInput
open MeasureTheory Set Filter

noncomputable def firstParametricLaw (i : NestedInput) (htv : i.t ≤ i.v) (ρ : ProbabilityMeasure ℝ) : Mixed 3 :=
  averagedLaw ρ (i.firstConditionalLaw htv) (i.measurable_firstConditionalLaw htv)

theorem firstParametricLaw_fullBudget (i : NestedInput) (htv : i.t ≤ i.v) (ρ : ProbabilityMeasure ℝ)
    (hρ : ∀ᵐ s ∂(ρ : Measure ℝ), s ∈ Icc 0 i.t) :
    ∀ᵐ x ∂(i.firstParametricLaw htv ρ : Measure (Allocation 3)), FullBudget i.M x := by
  apply averagedLaw_fullBudget
  exact hρ.mono (fun _ hs => i.firstConditionalLaw_fullBudget htv hs)

theorem firstParametricLaw_uniforms (i : NestedInput) (htv : i.t ≤ i.v) (ρ : ProbabilityMeasure ℝ)
    (hρ : ∀ᵐ s ∂(ρ : Measure ℝ), s ∈ Icc 0 i.t) :
    (marginal (i.firstParametricLaw htv ρ) 0 : Measure ℝ) = uniformLaw i.a ∧
      (marginal (i.firstParametricLaw htv ρ) 1 : Measure ℝ) = uniformLaw i.d := by
  constructor
  · apply averagedLaw_marginal_constant
    exact hρ.mono (fun _ hs => (i.firstConditionalLaw_marginals htv hs).1)
  · apply averagedLaw_marginal_constant
    exact hρ.mono (fun _ hs => (i.firstConditionalLaw_marginals htv hs).2.1)

theorem firstParametricLaw_thirdCDF (i : NestedInput) (htv : i.t ≤ i.v) (ρ : ProbabilityMeasure ℝ)
    (hρ : ∀ᵐ s ∂(ρ : Measure ℝ), s ∈ Icc 0 i.t) {z : ℝ} (hzc : z ≤ i.c) :
    (marginal (i.firstParametricLaw htv ρ) 2 : Measure ℝ).real (Iic z) =
      ∫ s, i.conditionalCDF s z ∂(ρ : Measure ℝ) := by
  have he : (fun s => (marginal (i.firstConditionalLaw htv s) 2 : Measure ℝ)) =ᵐ[(ρ : Measure ℝ)]
      i.conditionalThirdLaw := hρ.mono (fun _ hs => (i.firstConditionalLaw_marginals htv hs).2.2)
  rw [firstParametricLaw, averagedLaw_marginal, Measure.bind_congr_right he]
  have hi : Integrable (fun s => i.conditionalCDF s z) (ρ : Measure ℝ) := by
    apply (integrable_const (1 : ℝ)).mono' (i.measurable_conditionalCDF z).aestronglyMeasurable
    exact hρ.mono (fun s hs => by
      have hb := i.conditionalCDF_bounds htv hs hzc
      simpa only [Real.norm_eq_abs, abs_of_nonneg hb.1] using hb.2)
  have hn : 0 ≤ᵐ[(ρ : Measure ℝ)] (fun s => i.conditionalCDF s z) :=
    hρ.mono (fun _ hs => (i.conditionalCDF_bounds htv hs hzc).1)
  have hp : ((ρ : Measure ℝ).bind i.conditionalThirdLaw) (Iic z) =
      ENNReal.ofReal (∫ s, i.conditionalCDF s z ∂(ρ : Measure ℝ)) := by
    rw [Measure.bind_apply measurableSet_Iic i.measurable_conditionalThirdLaw.aemeasurable]
    calc
      _ = ∫⁻ s, ENNReal.ofReal (i.conditionalCDF s z) ∂(ρ : Measure ℝ) :=
        lintegral_congr_ae (hρ.mono (fun _ hs => i.conditionalThirdLaw_Iic htv hs hzc))
      _ = _ := (ofReal_integral_eq_lintegral_ofReal hi hn).symm
  rw [Measure.real, hp, ENNReal.toReal_ofReal (integral_nonneg_of_ae hn)]

theorem firstParametricLaw_thirdCDF_above (i : NestedInput) (htv : i.t ≤ i.v) (ρ : ProbabilityMeasure ℝ)
    (hρ : ∀ᵐ s ∂(ρ : Measure ℝ), s ∈ Icc 0 i.t) {z : ℝ} (hcz : i.c ≤ z) :
    (marginal (i.firstParametricLaw htv ρ) 2 : Measure ℝ).real (Iic z) = 1 := by
  have hc : (marginal (i.firstParametricLaw htv ρ) 2 : Measure ℝ).real (Iic i.c) = 1 := by
    rw [i.firstParametricLaw_thirdCDF htv ρ hρ le_rfl]
    have he : (fun s => i.conditionalCDF s i.c) =ᵐ[(ρ : Measure ℝ)] (fun _ => 1) := by
      apply hρ.mono
      intro s hs
      have hsc : s ≤ i.c := hs.2.trans (le_of_lt i.t_lt)
      simp [conditionalCDF, hsc]
    rw [integral_congr_ae he, integral_const, probReal_univ, one_smul]
  have hm := measureReal_mono (μ := (marginal (i.firstParametricLaw htv ρ) 2 : Measure ℝ))
    (Iic_subset_Iic.mpr hcz)
  exact le_antisymm measureReal_le_one (by simpa only [hc] using hm)

theorem firstParametricLaw_CDFClose (i : NestedInput) (htv : i.t ≤ i.v) (ρ σ : ProbabilityMeasure ℝ)
    (hρ : ∀ᵐ s ∂(ρ : Measure ℝ), s ∈ Icc 0 i.t) (hσ : ∀ᵐ s ∂(σ : Measure ℝ), s ∈ Icc 0 i.t)
    {δ : ℝ} (hc : RealCDFClose ρ σ δ) :
    CDFClose (i.firstParametricLaw htv ρ) (i.firstParametricLaw htv σ) (2 * δ) := by
  have huρ := i.firstParametricLaw_uniforms htv ρ hρ
  have huσ := i.firstParametricLaw_uniforms htv σ hσ
  have hn : 0 ≤ 2 * δ := mul_nonneg (by norm_num) hc.nonnegative
  intro j z
  unfold closedCDF
  fin_cases j
  · change |(marginal (i.firstParametricLaw htv ρ) 0 : Measure ℝ).real (Iic z) -
      (marginal (i.firstParametricLaw htv σ) 0 : Measure ℝ).real (Iic z)| ≤ _
    rw [huρ.1, huσ.1]
    simpa only [sub_self, abs_zero] using hn
  · change |(marginal (i.firstParametricLaw htv ρ) 1 : Measure ℝ).real (Iic z) -
      (marginal (i.firstParametricLaw htv σ) 1 : Measure ℝ).real (Iic z)| ≤ _
    rw [huρ.2, huσ.2]
    simpa only [sub_self, abs_zero] using hn
  · change |(marginal (i.firstParametricLaw htv ρ) 2 : Measure ℝ).real (Iic z) -
      (marginal (i.firstParametricLaw htv σ) 2 : Measure ℝ).real (Iic z)| ≤ _
    by_cases hzc : z ≤ i.c
    · rw [i.firstParametricLaw_thirdCDF htv ρ hρ hzc, i.firstParametricLaw_thirdCDF htv σ hσ hzc]
      exact i.conditionalCDF_expectation_error htv ρ σ hc hρ hσ hzc
    · rw [i.firstParametricLaw_thirdCDF_above htv ρ hρ (le_of_lt (lt_of_not_ge hzc)),
        i.firstParametricLaw_thirdCDF_above htv σ hσ (le_of_lt (lt_of_not_ge hzc))]
      simpa only [sub_self, abs_zero] using hn

noncomputable def firstLocationApproximation (i : NestedInput) (htv : i.t ≤ i.v) (K : ℕ) : Mixed 3 :=
  i.firstParametricLaw htv (i.dyadicLocationLaw K)

theorem firstLocationApproximation_CDF_error (i : NestedInput) (htv : i.t ≤ i.v) (K : ℕ) :
    CDFClose (i.firstLocationApproximation htv K) (i.firstLaw htv) (1 / (2 : ℝ) ^ K) := by
  have he := i.firstParametricLaw_CDFClose htv _ _ (i.dyadicLocationLaw_supported K) i.locationLaw_supported
    (i.dyadicLocationLaw_CDF_error K)
  have hr : 2 * (1 / (2 * (2 : ℝ) ^ K)) = 1 / (2 : ℝ) ^ K := by field_simp
  rw [hr] at he
  exact he

theorem firstLocationApproximation_fullBudget (i : NestedInput) (htv : i.t ≤ i.v) (K : ℕ) :
    ∀ᵐ x ∂(i.firstLocationApproximation htv K : Measure (Allocation 3)), FullBudget i.M x :=
  i.firstParametricLaw_fullBudget htv _ (i.dyadicLocationLaw_supported K)

end Blotto.NestedInput
