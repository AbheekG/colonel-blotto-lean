import Blotto.NestedConditional

/-! Exact integration of the conditional third-coordinate CDF in the first
nested case. The calculation uses the actual location measure. -/

namespace Blotto.NestedInput
open MeasureTheory Set Filter
open scoped Interval

noncomputable def cdfPrimitive (i : NestedInput) (z s : ℝ) : ℝ :=
  i.locationCDF s + (i.c - z) * (i.h * (i.h + i.t) / i.t) /
    ((i.h + s) * (i.c - s))

noncomputable def cdfDensity (i : NestedInput) (z s : ℝ) : ℝ :=
  i.locationDensity s * (1 - (i.c - i.h - 2 * s) * (i.c - z) / (i.c - s) ^ 2)

theorem hasDerivAt_cdfPrimitive (i : NestedInput) {s : ℝ} (hs0 : 0 ≤ s) (hsc : s < i.c)
    (z : ℝ) : HasDerivAt (i.cdfPrimitive z) (i.cdfDensity z s) s := by
  have hh := i.h_pos
  have ht := i.t_pos
  have hhs : i.h + s ≠ 0 := ne_of_gt (by linarith)
  have hcs : i.c - s ≠ 0 := ne_of_gt (sub_pos.mpr hsc)
  have hder := i.hasDerivAt_locationCDF hs0
  have hden := ((hasDerivAt_const s i.h).add (hasDerivAt_id s)).mul
    ((hasDerivAt_const s i.c).sub (hasDerivAt_id s))
  have hq := (hasDerivAt_const s ((i.c - z) * (i.h * (i.h + i.t) / i.t))).div
    hden (mul_ne_zero hhs hcs)
  convert hder.add hq using 1
  · ext y
    rfl
  · dsimp [cdfDensity, locationDensity]
    field_simp [ne_of_gt ht, hhs, hcs]
    ring

theorem continuousOn_cdfDensity (i : NestedInput) {b : ℝ} (hbc : b < i.c) (z : ℝ) :
    ContinuousOn (i.cdfDensity z) (Icc 0 b) := by
  apply (i.continuousOn_locationDensity b).mul
  apply continuousOn_const.sub
  apply ContinuousOn.div
  · exact (continuousOn_const.sub (continuousOn_const.mul continuousOn_id)).mul continuousOn_const
  · exact (continuousOn_const.sub continuousOn_id).pow 2
  · intro s hs
    change (i.c - s) ^ 2 ≠ 0
    exact pow_ne_zero _ (ne_of_gt (by linarith [hs.2]))

theorem integral_cdfDensity (i : NestedInput) {b : ℝ} (hb : 0 ≤ b) (hbc : b < i.c)
    (z : ℝ) : (∫ s in (0 : ℝ)..b, i.cdfDensity z s) = i.cdfPrimitive z b - i.cdfPrimitive z 0 := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro s hs
    have hsb : s ∈ Icc 0 b := by simpa only [uIcc_of_le hb] using hs
    exact i.hasDerivAt_cdfPrimitive hsb.1 (lt_of_le_of_lt hsb.2 hbc) z
  · exact ContinuousOn.intervalIntegrable_of_Icc hb (i.continuousOn_cdfDensity hbc z)

/-- Integrate only up to min(z,t); conditional CDFs vanish above z. -/
theorem integral_conditionalCDF (i : NestedInput) {z : ℝ} (hz0 : 0 ≤ z) (_hzc : z ≤ i.c) :
    (∫ s, i.conditionalCDF s z ∂(i.locationLaw : Measure ℝ)) =
      i.cdfPrimitive z (min z i.t) - i.cdfPrimitive z 0 := by
  have hb : 0 ≤ min z i.t := le_min hz0 (le_of_lt i.t_pos)
  have hbc : min z i.t < i.c := lt_of_le_of_lt (min_le_right _ _) i.t_lt
  have hi : Iic z ∩ Icc 0 i.t = Icc 0 (min z i.t) := by
    ext s
    simp only [mem_inter_iff, mem_Iic, mem_Icc, le_min_iff]
    tauto
  rw [i.integral_locationLaw]
  have he : (fun s => i.locationDensity s * i.conditionalCDF s z) =
      (Iic z).indicator (i.cdfDensity z) := by
    funext s
    by_cases hs : s ≤ z
    · simp [conditionalCDF, cdfDensity, hs]
    · simp [conditionalCDF, hs]
  rw [he, integral_indicator measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic, hi,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hb, i.integral_cdfDensity hb hbc]

noncomputable def nestedCDF (i : NestedInput) (z : ℝ) : ℝ :=
  i.q * (max (min z i.t) 0 / i.t) + (1 - i.q) * (max (min z i.c) 0 / i.c)

noncomputable def nestedTargetLaw (i : NestedInput) : Measure ℝ :=
  ENNReal.ofReal i.q • uniformLaw i.t + ENNReal.ofReal (1 - i.q) • uniformLaw i.c

theorem nestedTargetLaw_probability (i : NestedInput) : IsProbabilityMeasure i.nestedTargetLaw := by
  let : IsProbabilityMeasure (uniformLaw i.t) := (uniformMarginal i.t i.t_pos).property
  let : IsProbabilityMeasure (uniformLaw i.c) := (uniformMarginal i.c i.c_pos).property
  constructor
  simp only [nestedTargetLaw, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add (le_of_lt i.q_pos) (sub_nonneg.mpr (le_of_lt i.q_lt))]
  norm_num

theorem nestedTargetLaw_Iic (i : NestedInput) (z : ℝ) :
    i.nestedTargetLaw (Iic z) = ENNReal.ofReal (i.nestedCDF z) := by
  let : IsProbabilityMeasure (uniformLaw i.t) := (uniformMarginal i.t i.t_pos).property
  let : IsProbabilityMeasure (uniformLaw i.c) := (uniformMarginal i.c i.c_pos).property
  have htCDF : (uniformLaw i.t).real (Iic z) = max (min z i.t) 0 / i.t := by
    simpa only [uniformMarginal, ProbabilityMeasure.coe_mk] using uniform_closedCDF i.t i.t_pos z
  have hcCDF : (uniformLaw i.c).real (Iic z) = max (min z i.c) 0 / i.c := by
    simpa only [uniformMarginal, ProbabilityMeasure.coe_mk] using uniform_closedCDF i.c i.c_pos z
  rw [nestedTargetLaw, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    smul_eq_mul, smul_eq_mul,
    ← ofReal_measureReal (measure_ne_top (uniformLaw i.t) (Iic z)),
    ← ofReal_measureReal (measure_ne_top (uniformLaw i.c) (Iic z)),
    htCDF, hcCDF,
    ← ENNReal.ofReal_mul (le_of_lt i.q_pos),
    ← ENNReal.ofReal_mul (sub_nonneg.mpr (le_of_lt i.q_lt)),
    ← ENNReal.ofReal_add
      (mul_nonneg (le_of_lt i.q_pos) (div_nonneg (le_max_right _ _) (le_of_lt i.t_pos)))
      (mul_nonneg (sub_nonneg.mpr (le_of_lt i.q_lt)) (div_nonneg (le_max_right _ _) (le_of_lt i.c_pos)))]
  rfl

/-- The exact integral is the desired nested-uniform CDF; no density matching
or boundary limit is left implicit. -/
theorem integral_conditionalCDF_target (i : NestedInput) {z : ℝ}
    (hz0 : 0 ≤ z) (hzc : z ≤ i.c) :
    (∫ s, i.conditionalCDF s z ∂(i.locationLaw : Measure ℝ)) = i.nestedCDF z := by
  rw [i.integral_conditionalCDF hz0 hzc]
  have hh := ne_of_gt i.h_pos
  have ht := ne_of_gt i.t_pos
  have hc := ne_of_gt i.c_pos
  have hht := ne_of_gt (add_pos i.h_pos i.t_pos)
  have hct := ne_of_gt (sub_pos.mpr i.t_lt)
  have hhz : i.h + z ≠ 0 := ne_of_gt (add_pos_of_pos_of_nonneg i.h_pos hz0)
  unfold nestedCDF
  rw [min_eq_left hzc, max_eq_left hz0]
  by_cases hzt : z ≤ i.t
  · have hcz : i.c - z ≠ 0 := ne_of_gt (sub_pos.mpr (lt_of_le_of_lt hzt i.t_lt))
    rw [min_eq_left hzt, max_eq_left hz0]
    dsimp [cdfPrimitive, locationCDF]
    field_simp [hh, ht, hc, hht, hct, hhz, hcz]
    dsimp [h]
    ring
  · rw [min_eq_right (le_of_lt (lt_of_not_ge hzt)), max_eq_left (le_of_lt i.t_pos)]
    dsimp [cdfPrimitive, locationCDF]
    field_simp [hh, ht, hc, hht, hct]
    dsimp [h]
    ring

theorem averagedThirdLaw_Iic_inside (i : NestedInput) (htv : i.t ≤ i.v) {z : ℝ}
    (hz0 : 0 ≤ z) (hzc : z ≤ i.c) :
    i.averagedThirdLaw (Iic z) = i.nestedTargetLaw (Iic z) := by
  rw [i.averagedThirdLaw_Iic_integral htv hzc, i.integral_conditionalCDF_target hz0 hzc,
    i.nestedTargetLaw_Iic]

theorem averagedThirdLaw_Iic_below (i : NestedInput) (htv : i.t ≤ i.v) {z : ℝ}
    (hz : z < 0) : i.averagedThirdLaw (Iic z) = i.nestedTargetLaw (Iic z) := by
  have hzc : z ≤ i.c := le_of_lt (lt_trans hz i.c_pos)
  have he : (fun s => i.conditionalCDF s z) =ᵐ[(i.locationLaw : Measure ℝ)] (fun _ => 0) := by
    apply i.locationLaw_supported.mono
    intro s hs
    simp [conditionalCDF, not_le.mpr (lt_of_lt_of_le hz hs.1)]
  rw [i.averagedThirdLaw_Iic_integral htv hzc, integral_congr_ae he, integral_zero,
    ENNReal.ofReal_zero, i.nestedTargetLaw_Iic]
  simp [nestedCDF, min_eq_left (le_of_lt (lt_trans hz i.t_pos)),
    min_eq_left (le_of_lt (lt_trans hz i.c_pos)), max_eq_right (le_of_lt hz)]

/-- The actual averaged scalar measure has exactly the prescribed nested law
in the first case of Lemma 2.3. Whole-allocation assembly is proved separately. -/
theorem averagedThirdLaw_eq_target (i : NestedInput) (htv : i.t ≤ i.v) :
    i.averagedThirdLaw = i.nestedTargetLaw := by
  let : IsProbabilityMeasure i.averagedThirdLaw := i.averagedThirdLaw_probability htv
  let : IsProbabilityMeasure i.nestedTargetLaw := i.nestedTargetLaw_probability
  apply Measure.ext_of_Iic
  intro z
  by_cases hz : z < 0
  · exact i.averagedThirdLaw_Iic_below htv hz
  · have hz0 := le_of_not_gt hz
    by_cases hzc : z ≤ i.c
    · exact i.averagedThirdLaw_Iic_inside htv hz0 hzc
    · have hcz := le_of_lt (lt_of_not_ge hzc)
      have hc : i.nestedTargetLaw (Iic i.c) = 1 := by
        rw [i.nestedTargetLaw_Iic]
        simp [nestedCDF, min_eq_right (le_of_lt i.t_lt), min_self,
          max_eq_left (le_of_lt i.t_pos), max_eq_left (le_of_lt i.c_pos),
          div_self (ne_of_gt i.t_pos), div_self (ne_of_gt i.c_pos)]
      have ha : i.averagedThirdLaw (Iic i.c) = 1 :=
        (i.averagedThirdLaw_Iic_inside htv (le_of_lt i.c_pos) le_rfl).trans hc
      have hsub : Iic i.c ⊆ Iic z := fun _ hx => le_trans hx hcz
      have heA : i.averagedThirdLaw (Iic z) = 1 := le_antisymm
        (by simpa only [measure_univ] using measure_mono (μ := i.averagedThirdLaw) (subset_univ (Iic z)))
        (by simpa only [ha] using measure_mono (μ := i.averagedThirdLaw) hsub)
      have heT : i.nestedTargetLaw (Iic z) = 1 := le_antisymm
        (by simpa only [measure_univ] using measure_mono (μ := i.nestedTargetLaw) (subset_univ (Iic z)))
        (by simpa only [hc] using measure_mono (μ := i.nestedTargetLaw) hsub)
      exact heA.trans heT.symm

end Blotto.NestedInput
