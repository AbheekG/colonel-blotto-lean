import Blotto.NestedInput

/-! The first nested-uniform branch's explicit location draw. Its actual
push-forward law and CDF are proved here; averaging the conditional allocation
laws is a separate remaining obligation. -/

namespace Blotto.NestedInput
open MeasureTheory Set Filter

theorem measurable_location (i : NestedInput) : Measurable i.location :=
  ((measurable_const.mul measurable_id).div
    (measurable_const.sub (measurable_const.mul measurable_id)))

noncomputable def locationLaw (i : NestedInput) : ProbabilityMeasure ℝ :=
  unitUniform.map i.location

theorem locationLaw_supported (i : NestedInput) :
    ∀ᵐ s ∂(i.locationLaw : Measure ℝ), s ∈ Icc 0 i.t := by
  change ∀ᵐ s ∂Measure.map i.location (unitUniform : Measure ℝ), 0 ≤ s ∧ s ≤ i.t
  rw [ae_map_iff i.measurable_location.aemeasurable measurableSet_Icc]
  exact unitUniform_supported.mono fun _ hs => i.location_bounds hs

noncomputable def locationCDF (i : NestedInput) (s : ℝ) : ℝ :=
  s * (i.h + i.t) / (i.t * (i.h + s))

theorem locationCDF_bounds (i : NestedInput) {s : ℝ} (hs : 0 ≤ s ∧ s ≤ i.t) :
    0 ≤ i.locationCDF s ∧ i.locationCDF s ≤ 1 := by
  have hd : 0 < i.t * (i.h + s) := mul_pos i.t_pos (by linarith [i.h_pos])
  constructor
  · exact div_nonneg (mul_nonneg hs.1 (le_of_lt (add_pos i.h_pos i.t_pos))) (le_of_lt hd)
  · apply (div_le_one hd).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hs.2) (le_of_lt i.h_pos)]

theorem locationLaw_closedCDF_inside (i : NestedInput) {s : ℝ}
    (hs : 0 ≤ s ∧ s ≤ i.t) :
    (i.locationLaw : Measure ℝ).real (Iic s) = i.locationCDF s := by
  have he : (i.location ⁻¹' Iic s) =ᵐ[(unitUniform : Measure ℝ)] Iic (i.locationCDF s) := by
    apply unitUniform_supported.mono
    intro r hr
    apply propext
    exact i.location_threshold hr hs
  change (Measure.map i.location (unitUniform : Measure ℝ)).real (Iic s) = _
  rw [map_measureReal_apply i.measurable_location measurableSet_Iic,
    measureReal_congr he, unitUniform_closedCDF]
  rw [min_eq_left (i.locationCDF_bounds hs).2, max_eq_left (i.locationCDF_bounds hs).1]

theorem locationLaw_closedCDF_below (i : NestedInput) {s : ℝ} (hs : s < 0) :
    (i.locationLaw : Measure ℝ).real (Iic s) = 0 := by
  have he : (i.location ⁻¹' Iic s) =ᵐ[(unitUniform : Measure ℝ)] Iic (-1 : ℝ) := by
    apply unitUniform_supported.mono
    intro r hr
    apply propext
    have hloc := i.location_bounds hr
    rcases hr with ⟨hr0, hr1⟩
    simp only [mem_preimage, mem_Iic]
    constructor <;> intro h <;> linarith
  change (Measure.map i.location (unitUniform : Measure ℝ)).real (Iic s) = _
  rw [map_measureReal_apply i.measurable_location measurableSet_Iic,
    measureReal_congr he, unitUniform_closedCDF]
  norm_num

theorem locationLaw_closedCDF_above (i : NestedInput) {s : ℝ} (hs : i.t ≤ s) :
    (i.locationLaw : Measure ℝ).real (Iic s) = 1 := by
  have he : (i.location ⁻¹' Iic s) =ᵐ[(unitUniform : Measure ℝ)] Iic (1 : ℝ) := by
    apply unitUniform_supported.mono
    intro r hr
    apply propext
    have hloc := i.location_bounds hr
    rcases hr with ⟨hr0, hr1⟩
    simp only [mem_preimage, mem_Iic]
    constructor <;> intro h <;> linarith
  change (Measure.map i.location (unitUniform : Measure ℝ)).real (Iic s) = _
  rw [map_measureReal_apply i.measurable_location measurableSet_Iic,
    measureReal_congr he, unitUniform_closedCDF]
  norm_num

/-- One global CDF formula; the argument is clamped before division so the
formula also applies at negative queries and at the rational map's pole. -/
theorem locationLaw_closedCDF (i : NestedInput) (s : ℝ) :
    (i.locationLaw : Measure ℝ).real (Iic s) = i.locationCDF (max (min s i.t) 0) := by
  by_cases hs : s < 0
  · rw [i.locationLaw_closedCDF_below hs,
      min_eq_left (by linarith [i.t_pos] : s ≤ i.t), max_eq_right (le_of_lt hs)]
    simp [locationCDF]
  · have hs0 := le_of_not_gt hs
    by_cases hst : s ≤ i.t
    · rw [min_eq_left hst, max_eq_left hs0]
      exact i.locationLaw_closedCDF_inside ⟨hs0, hst⟩
    · have hts := le_of_lt (lt_of_not_ge hst)
      rw [i.locationLaw_closedCDF_above hts, min_eq_right hts, max_eq_left (le_of_lt i.t_pos)]
      symm
      dsimp [locationCDF]
      exact div_self (ne_of_gt (mul_pos i.t_pos (add_pos i.h_pos i.t_pos)))

/-- The location draw has a continuous CDF, including both support endpoints. -/
theorem continuous_locationLaw_CDF (i : NestedInput) :
    Continuous (fun s => (i.locationLaw : Measure ℝ).real (Iic s)) := by
  have ht : Continuous (fun s : ℝ => max (min s i.t) 0) :=
    (continuous_id.min continuous_const).max continuous_const
  have he : (fun s => (i.locationLaw : Measure ℝ).real (Iic s)) =
      (fun s => i.locationCDF (max (min s i.t) 0)) := funext i.locationLaw_closedCDF
  rw [he]
  exact (ht.mul continuous_const).div (continuous_const.mul (continuous_const.add ht))
    fun s => ne_of_gt (mul_pos i.t_pos
      (add_pos_of_pos_of_nonneg i.h_pos (le_max_right _ _)))

/-- Averaging conditional atoms at the sampled location creates no atom. -/
theorem locationLaw_singleton (i : NestedInput) (s : ℝ) :
    (i.locationLaw : Measure ℝ) {s} = 0 := by
  have hc : Continuous (ProbabilityTheory.cdf (i.locationLaw : Measure ℝ)) := by
    have he : (fun s => ProbabilityTheory.cdf (i.locationLaw : Measure ℝ) s) =
        (fun s => (i.locationLaw : Measure ℝ).real (Iic s)) :=
      funext (ProbabilityTheory.cdf_eq_real (i.locationLaw : Measure ℝ))
    change Continuous (fun s => ProbabilityTheory.cdf (i.locationLaw : Measure ℝ) s)
    rw [he]
    exact i.continuous_locationLaw_CDF
  rw [← ProbabilityTheory.measure_cdf (i.locationLaw : Measure ℝ),
    StieltjesFunction.measure_singleton, hc.continuousAt.continuousWithinAt.leftLim_eq,
    sub_self, ENNReal.ofReal_zero]

end Blotto.NestedInput
