import Blotto.NestedCalculus

/-! Identifies the explicit location draw with its normalized Lebesgue-density
law. This makes the subsequent conditional averaging a statement about the
actual sampled distribution, rather than a formal density calculation. -/

namespace Blotto.NestedInput
open MeasureTheory Set Filter
open scoped Interval

theorem continuousOn_locationDensity (i : NestedInput) (b : ℝ) :
    ContinuousOn i.locationDensity (Icc 0 b) := by
  apply continuousOn_const.div
    (continuousOn_const.mul ((continuousOn_const.add continuousOn_id).pow 2))
  intro s hs
  change i.t * (i.h + s) ^ 2 ≠ 0
  exact mul_ne_zero (ne_of_gt i.t_pos)
    (pow_ne_zero _ (ne_of_gt (by linarith [i.h_pos, hs.1])))

theorem locationDensity_integrable (i : NestedInput) (b : ℝ) :
    IntegrableOn i.locationDensity (Icc 0 b) volume :=
  (i.continuousOn_locationDensity b).integrableOn_Icc

noncomputable def densityMeasure (i : NestedInput) : Measure ℝ :=
  (volume.restrict (Icc 0 i.t)).withDensity (fun s => ENNReal.ofReal (i.locationDensity s))

theorem densityMeasure_Iic (i : NestedInput) (z : ℝ) :
    i.densityMeasure (Iic z) = ENNReal.ofReal (i.locationCDF (max (min z i.t) 0)) := by
  have hi : Iic z ∩ Icc 0 i.t = Icc 0 (min z i.t) := by
    ext s
    simp only [mem_inter_iff, mem_Iic, mem_Icc, le_min_iff]
    tauto
  rw [densityMeasure, withDensity_apply _ measurableSet_Iic,
    Measure.restrict_restrict measurableSet_Iic, hi]
  by_cases hz : 0 ≤ z
  · have hb : 0 ≤ min z i.t := le_min hz (le_of_lt i.t_pos)
    have hnn : 0 ≤ᵐ[volume.restrict (Icc 0 (min z i.t))] i.locationDensity :=
      (ae_restrict_mem measurableSet_Icc).mono fun s hs => i.locationDensity_nonnegative hs.1
    rw [← ofReal_integral_eq_lintegral_ofReal (i.locationDensity_integrable _) hnn,
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hb,
      i.integral_locationDensity hb, max_eq_left hb]
  · have hn : min z i.t < 0 := lt_of_le_of_lt (min_le_left _ _) (lt_of_not_ge hz)
    rw [Icc_eq_empty_of_lt hn, Measure.restrict_empty, lintegral_zero_measure,
      max_eq_right (le_of_lt hn)]
    simp [locationCDF]

/-- Exact equality of measures, hence equality of all measurable-event laws. -/
theorem locationLaw_withDensity (i : NestedInput) :
    (i.locationLaw : Measure ℝ) = i.densityMeasure := by
  apply Measure.ext_of_Iic
  intro z
  have he := ofReal_measureReal (measure_ne_top (i.locationLaw : Measure ℝ) (Iic z))
  rw [← he, i.locationLaw_closedCDF, i.densityMeasure_Iic]

/-- The density is normalized because it is the actual probability law of the
rational inverse-CDF draw. -/
theorem densityMeasure_mass (i : NestedInput) : i.densityMeasure univ = 1 := by
  rw [← i.locationLaw_withDensity]
  exact measure_univ

theorem measurable_locationDensity (i : NestedInput) : Measurable i.locationDensity :=
  measurable_const.div (measurable_const.mul ((measurable_const.add measurable_id).pow_const 2))

/-- The rational density is nonnegative everywhere; its value at the single
pole is zero under Lean's totalized real division. -/
theorem locationDensity_nonnegative_all (i : NestedInput) (s : ℝ) : 0 ≤ i.locationDensity s := by
  have hh := i.h_pos
  have ht := i.t_pos
  dsimp [locationDensity]
  positivity

theorem integral_locationLaw (i : NestedInput) (f : ℝ → ℝ) :
    (∫ s, f s ∂(i.locationLaw : Measure ℝ)) =
      ∫ s in Icc 0 i.t, i.locationDensity s * f s := by
  rw [i.locationLaw_withDensity, densityMeasure,
    integral_withDensity_eq_integral_toReal_smul i.measurable_locationDensity.ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (i.locationDensity_nonnegative_all _), smul_eq_mul]

end Blotto.NestedInput
