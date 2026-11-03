import Blotto.NestedDensity
import Blotto.ParameterLaw

/-! The first nested case's actual conditional scalar laws. A measurable
family and its probability normalization are explicit before averaging. -/

namespace Blotto.NestedInput
open MeasureTheory Set Filter

noncomputable def conditionalThirdLaw (i : NestedInput) (s : ℝ) : Measure ℝ :=
  ENNReal.ofReal (1 - i.conditionalProbability s) • Measure.dirac s +
    ENNReal.ofReal (i.conditionalProbability s) • (affineUniform s i.c : Measure ℝ)

theorem measurable_conditionalProbability (i : NestedInput) : Measurable i.conditionalProbability :=
  (measurable_const.sub (measurable_const.mul measurable_id)).div
    (measurable_const.sub measurable_id)

theorem measurable_conditionalThirdLaw (i : NestedInput) : Measurable i.conditionalThirdLaw :=
  (measurable_weighted_law (measurable_const.sub i.measurable_conditionalProbability)
    Measure.measurable_dirac).add
    (measurable_weighted_law i.measurable_conditionalProbability
      (measurable_affineUniform_family measurable_id measurable_const))

theorem conditionalThirdLaw_probability (i : NestedInput) (htv : i.t ≤ i.v) {s : ℝ}
    (hs : 0 ≤ s ∧ s ≤ i.t) : IsProbabilityMeasure (i.conditionalThirdLaw s) := by
  constructor
  have hp := i.conditional_bounds htv hs
  have h1p := sub_nonneg.mpr hp.2
  simp only [conditionalThirdLaw, Measure.add_apply, Measure.smul_apply,
    measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add h1p hp.1]
  norm_num

noncomputable def averagedThirdLaw (i : NestedInput) : Measure ℝ :=
  (i.locationLaw : Measure ℝ).bind i.conditionalThirdLaw

theorem averagedThirdLaw_probability (i : NestedInput) (htv : i.t ≤ i.v) :
    IsProbabilityMeasure i.averagedThirdLaw := by
  apply isProbabilityMeasure_bind i.measurable_conditionalThirdLaw.aemeasurable
  exact i.locationLaw_supported.mono fun _ hs => i.conditionalThirdLaw_probability htv hs

noncomputable def conditionalCDF (i : NestedInput) (s z : ℝ) : ℝ :=
  if s ≤ z then 1 - (i.c - i.h - 2 * s) * (i.c - z) / (i.c - s) ^ 2 else 0

/-- The conditional CDF below the top endpoint, with the atom at s included. -/
theorem conditionalThirdLaw_Iic (i : NestedInput) (htv : i.t ≤ i.v) {s z : ℝ}
    (hs : 0 ≤ s ∧ s ≤ i.t) (hz : z ≤ i.c) :
    i.conditionalThirdLaw s (Iic z) = ENNReal.ofReal (i.conditionalCDF s z) := by
  have hp := i.conditional_bounds htv hs
  have hsc : s < i.c := lt_of_le_of_lt hs.2 i.t_lt
  have h1p := sub_nonneg.mpr hp.2
  rw [conditionalThirdLaw, Measure.add_apply, Measure.smul_apply,
    Measure.smul_apply, smul_eq_mul, smul_eq_mul]
  by_cases hsz : s ≤ z
  · rw [Measure.dirac_apply' s measurableSet_Iic]
    simp only [mem_Iic, hsz, indicator_of_mem, Pi.one_apply, mul_one]
    have he := ofReal_measureReal (measure_ne_top (affineUniform s i.c : Measure ℝ) (Iic z))
    rw [← he, affineUniform_closedCDF_increasing hsc, min_eq_left hz,
      max_eq_left (sub_nonneg.mpr hsz), ← ENNReal.ofReal_mul hp.1]
    have hratio : 0 ≤ (z - s) / (i.c - s) := div_nonneg (sub_nonneg.mpr hsz) (le_of_lt (sub_pos.mpr hsc))
    rw [← ENNReal.ofReal_add h1p (mul_nonneg hp.1 hratio)]
    congr 1
    rw [conditionalCDF, ite_eq_left hsz, conditionalProbability]
    field_simp [ne_of_gt (sub_pos.mpr hsc)]
    ring
  · have hdirac : (Measure.dirac s : Measure ℝ) (Iic z) = 0 := by simp [hsz]
    rw [hdirac, mul_zero, zero_add]
    have he := ofReal_measureReal (measure_ne_top (affineUniform s i.c : Measure ℝ) (Iic z))
    rw [← he, affineUniform_closedCDF_increasing hsc, min_eq_left hz,
      max_eq_right (by linarith : z - s ≤ 0), zero_div, ENNReal.ofReal_zero, mul_zero]
    simp [conditionalCDF, hsz]

theorem conditionalCDF_affine (i : NestedInput) {s z : ℝ}
    (hs : 0 ≤ s ∧ s ≤ i.t) (hsz : s ≤ z) :
    i.conditionalCDF s z = (1 - i.conditionalProbability s) +
      i.conditionalProbability s * ((z - s) / (i.c - s)) := by
  have hsc : 0 < i.c - s := by linarith [i.t_lt]
  rw [conditionalCDF, ite_eq_left hsz, conditionalProbability]
  field_simp [ne_of_gt hsc]
  ring

theorem conditionalCDF_bounds (i : NestedInput) (htv : i.t ≤ i.v) {s z : ℝ}
    (hs : 0 ≤ s ∧ s ≤ i.t) (hz : z ≤ i.c) :
    0 ≤ i.conditionalCDF s z ∧ i.conditionalCDF s z ≤ 1 := by
  have hp := i.conditional_bounds htv hs
  by_cases hsz : s ≤ z
  · rw [i.conditionalCDF_affine hs hsz]
    have hsc : 0 < i.c - s := by linarith [i.t_lt]
    have h0 : 0 ≤ (z - s) / (i.c - s) := div_nonneg (sub_nonneg.mpr hsz) (le_of_lt hsc)
    have h1 : (z - s) / (i.c - s) ≤ 1 := (div_le_one hsc).mpr (by linarith)
    have hm := mul_le_mul_of_nonneg_left h1 hp.1
    exact ⟨add_nonneg (sub_nonneg.mpr hp.2) (mul_nonneg hp.1 h0), by linarith⟩
  · simp [conditionalCDF, hsz]

theorem measurable_conditionalCDF (i : NestedInput) (z : ℝ) :
    Measurable (fun s => i.conditionalCDF s z) := by
  change Measurable ((Iic z).piecewise
    (fun s => 1 - (i.c - i.h - 2 * s) * (i.c - z) / (i.c - s) ^ 2) (fun _ => 0))
  apply Measurable.piecewise measurableSet_Iic _ measurable_const
  exact measurable_const.sub
    (((measurable_const.sub (measurable_const.mul measurable_id)).mul measurable_const).div
      ((measurable_const.sub measurable_id).pow_const 2))

theorem integrable_conditionalCDF (i : NestedInput) (htv : i.t ≤ i.v) {z : ℝ}
    (hz : z ≤ i.c) : Integrable (fun s => i.conditionalCDF s z) (i.locationLaw : Measure ℝ) := by
  apply (integrable_const (1 : ℝ)).mono' (i.measurable_conditionalCDF z).aestronglyMeasurable
  apply i.locationLaw_supported.mono
  intro s hs
  have hk := i.conditionalCDF_bounds htv hs hz
  simpa only [Real.norm_eq_abs, abs_of_nonneg hk.1] using hk.2

/-- The actual averaged event probability equals the integral of the conditional
CDF, with every normalization and measurability hypothesis checked. -/
theorem averagedThirdLaw_Iic_integral (i : NestedInput) (htv : i.t ≤ i.v) {z : ℝ}
    (hz : z ≤ i.c) :
    i.averagedThirdLaw (Iic z) =
      ENNReal.ofReal (∫ s, i.conditionalCDF s z ∂(i.locationLaw : Measure ℝ)) := by
  rw [averagedThirdLaw, Measure.bind_apply measurableSet_Iic i.measurable_conditionalThirdLaw.aemeasurable]
  calc
    _ = ∫⁻ s, ENNReal.ofReal (i.conditionalCDF s z) ∂(i.locationLaw : Measure ℝ) := by
      apply lintegral_congr_ae
      exact i.locationLaw_supported.mono fun s hs => i.conditionalThirdLaw_Iic htv hs hz
    _ = _ := (ofReal_integral_eq_lintegral_ofReal (i.integrable_conditionalCDF htv hz)
      (i.locationLaw_supported.mono fun _ hs => (i.conditionalCDF_bounds htv hs hz).1)).symm

end Blotto.NestedInput
