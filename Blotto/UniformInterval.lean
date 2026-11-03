import Blotto.Lotto

/-! Actual interval laws and affine images of a continuous unit-uniform draw.
Endpoints may coincide; that case is a Dirac law, not a zero-length density. -/

namespace Blotto

open MeasureTheory Set Filter

noncomputable def unitUniform : ProbabilityMeasure ℝ := uniformMarginal 1 (by norm_num)

noncomputable def affineLine (a b t : ℝ) : ℝ := (1 - t) * a + t * b

theorem measurable_affineLine (a b : ℝ) : Measurable (affineLine a b) :=
  ((measurable_const.sub measurable_id).mul measurable_const).add
    (measurable_id.mul measurable_const)

noncomputable def affineUniform (a b : ℝ) : ProbabilityMeasure ℝ :=
  unitUniform.map (affineLine a b)

noncomputable def intervalLaw (a b : ℝ) : Measure ℝ :=
  (ENNReal.ofReal (b - a))⁻¹ • volume.restrict (Icc a b)

noncomputable def intervalUniform (a b : ℝ) (hab : a < b) : ProbabilityMeasure ℝ :=
  ⟨intervalLaw a b, by
    constructor
    simp only [intervalLaw, Measure.smul_apply, Measure.restrict_apply_univ,
      Real.volume_Icc, smul_eq_mul]
    exact ENNReal.inv_mul_cancel (ne_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)))
      ENNReal.ofReal_ne_top⟩

theorem intervalUniform_closedCDF (a b : ℝ) (hab : a < b) (s : ℝ) :
    (intervalUniform a b hab : Measure ℝ).real (Iic s) =
      max (min s b - a) 0 / (b - a) := by
  have hi : Iic s ∩ Icc a b = Icc a (min s b) := by
    ext t
    simp only [mem_inter_iff, mem_Iic, mem_Icc, le_min_iff]
    tauto
  change (intervalLaw a b).real (Iic s) = _
  rw [intervalLaw, measureReal_ennreal_smul_apply]
  simp only [measureReal_def, Measure.restrict_apply measurableSet_Iic, hi,
    Real.volume_Icc, ENNReal.toReal_inv, ENNReal.toReal_ofReal (le_of_lt (sub_pos.mpr hab)),
    ENNReal.toReal_ofReal']
  ring

theorem unitUniform_closedCDF (s : ℝ) :
    (unitUniform : Measure ℝ).real (Iic s) = max (min s 1) 0 := by
  simpa [unitUniform] using uniform_closedCDF 1 (by norm_num) s

theorem unitUniform_strictCDF (s : ℝ) :
    (unitUniform : Measure ℝ).real (Iio s) = max (min s 1) 0 := by
  have he : (unitUniform : Measure ℝ).real (Iio s) =
      (unitUniform : Measure ℝ).real (Iic s) := by
    unfold Measure.real
    congr 1
    exact measure_congr (Iio_ae_eq_Iic' (uniform_singleton 1 s))
  rw [he, unitUniform_closedCDF]

theorem unitUniform_upperCDF (s : ℝ) :
    (unitUniform : Measure ℝ).real (Ici s) = 1 - max (min s 1) 0 := by
  have hi : Ici s = (Iio s)ᶜ := by ext t; simp
  rw [hi, measureReal_compl measurableSet_Iio, unitUniform_strictCDF, probReal_univ]

theorem affineUniform_constant (a : ℝ) :
    (affineUniform a a : Measure ℝ) = Measure.dirac a := by
  have hf : affineLine a a = fun _ => a := by
    funext t
    unfold affineLine
    ring
  change Measure.map (affineLine a a) (unitUniform : Measure ℝ) = _
  rw [hf, Measure.map_const]
  simp

theorem affineUniform_closedCDF_increasing {a b : ℝ} (hab : a < b) (s : ℝ) :
    (affineUniform a b : Measure ℝ).real (Iic s) =
      max (min s b - a) 0 / (b - a) := by
  have hd := sub_pos.mpr hab
  have hi : affineLine a b ⁻¹' Iic s = Iic ((s - a) / (b - a)) := by
    ext t
    simp only [mem_preimage, mem_Iic]
    rw [le_div_iff₀ hd]
    unfold affineLine
    constructor <;> intro h <;> nlinarith
  change (Measure.map (affineLine a b) (unitUniform : Measure ℝ)).real (Iic s) = _
  rw [map_measureReal_apply (measurable_affineLine a b) measurableSet_Iic, hi,
    unitUniform_closedCDF]
  by_cases hsa : s < a
  · have hr : (s - a) / (b - a) < 0 := div_neg_of_neg_of_pos (sub_neg.mpr hsa) hd
    rw [min_eq_left (by linarith : (s - a) / (b - a) ≤ 1),
      max_eq_right (le_of_lt hr), min_eq_left (le_trans (le_of_lt hsa) (le_of_lt hab)),
      max_eq_right (by linarith : s - a ≤ 0)]
    simp
  · have has := le_of_not_gt hsa
    by_cases hsb : s ≤ b
    · have hr0 : 0 ≤ (s - a) / (b - a) := div_nonneg (sub_nonneg.mpr has) (le_of_lt hd)
      have hr1 : (s - a) / (b - a) ≤ 1 := (div_le_one hd).mpr (by linarith)
      rw [min_eq_left hr1, max_eq_left hr0, min_eq_left hsb,
        max_eq_left (sub_nonneg.mpr has)]
    · have hbs := le_of_lt (lt_of_not_ge hsb)
      have hr1 : 1 ≤ (s - a) / (b - a) := (one_le_div hd).mpr (by linarith)
      rw [min_eq_right hr1, max_eq_left (by norm_num : (0 : ℝ) ≤ 1),
        min_eq_right hbs, max_eq_left (le_of_lt hd), div_self (ne_of_gt hd)]

theorem affineUniform_increasing {a b : ℝ} (hab : a < b) :
    (affineUniform a b : Measure ℝ) = intervalLaw a b := by
  change (affineUniform a b : Measure ℝ) = (intervalUniform a b hab : Measure ℝ)
  apply Measure.ext_of_Iic
  intro s
  have he : (affineUniform a b : Measure ℝ).real (Iic s) =
      (intervalUniform a b hab : Measure ℝ).real (Iic s) := by
    rw [affineUniform_closedCDF_increasing hab, intervalUniform_closedCDF]
  have hm := congrArg ENNReal.ofReal he
  rw [ofReal_measureReal (measure_ne_top (affineUniform a b : Measure ℝ) (Iic s)),
    ofReal_measureReal (measure_ne_top (intervalUniform a b hab : Measure ℝ) (Iic s))] at hm
  exact hm

theorem affineUniform_closedCDF_decreasing {a b : ℝ} (hba : b < a) (s : ℝ) :
    (affineUniform a b : Measure ℝ).real (Iic s) =
      max (min s a - b) 0 / (a - b) := by
  have hd := sub_pos.mpr hba
  have hi : affineLine a b ⁻¹' Iic s = Ici ((a - s) / (a - b)) := by
    ext t
    simp only [mem_preimage, mem_Iic, mem_Ici]
    rw [div_le_iff₀ hd]
    unfold affineLine
    constructor <;> intro h <;> nlinarith
  change (Measure.map (affineLine a b) (unitUniform : Measure ℝ)).real (Iic s) = _
  rw [map_measureReal_apply (measurable_affineLine a b) measurableSet_Iic, hi,
    unitUniform_upperCDF]
  by_cases hsb : s < b
  · have hr : 1 ≤ (a - s) / (a - b) := (one_le_div hd).mpr (by linarith)
    rw [min_eq_right hr, max_eq_left (by norm_num : (0 : ℝ) ≤ 1),
      min_eq_left (le_trans (le_of_lt hsb) (le_of_lt hba)),
      max_eq_right (by linarith : s - b ≤ 0)]
    simp
  · have hbs := le_of_not_gt hsb
    by_cases hsa : s ≤ a
    · have hr0 : 0 ≤ (a - s) / (a - b) := div_nonneg (sub_nonneg.mpr hsa) (le_of_lt hd)
      have hr1 : (a - s) / (a - b) ≤ 1 := (div_le_one hd).mpr (by linarith)
      rw [min_eq_left hr1, max_eq_left hr0, min_eq_left hsa,
        max_eq_left (sub_nonneg.mpr hbs)]
      field_simp [ne_of_gt hd]
      ring
    · have has := le_of_lt (lt_of_not_ge hsa)
      have hr0 : (a - s) / (a - b) ≤ 0 := div_nonpos_of_nonpos_of_nonneg
        (by linarith) (le_of_lt hd)
      rw [min_eq_left (by linarith : (a - s) / (a - b) ≤ 1), max_eq_right hr0,
        min_eq_right has, max_eq_left (le_of_lt hd), div_self (ne_of_gt hd)]
      norm_num

theorem affineUniform_decreasing {a b : ℝ} (hba : b < a) :
    (affineUniform a b : Measure ℝ) = intervalLaw b a := by
  change (affineUniform a b : Measure ℝ) = (intervalUniform b a hba : Measure ℝ)
  apply Measure.ext_of_Iic
  intro s
  have he : (affineUniform a b : Measure ℝ).real (Iic s) =
      (intervalUniform b a hba : Measure ℝ).real (Iic s) := by
    rw [affineUniform_closedCDF_decreasing hba, intervalUniform_closedCDF]
  have hm := congrArg ENNReal.ofReal he
  rw [ofReal_measureReal (measure_ne_top (affineUniform a b : Measure ℝ) (Iic s)),
    ofReal_measureReal (measure_ne_top (intervalUniform b a hba : Measure ℝ) (Iic s))] at hm
  exact hm

noncomputable def sortedIntervalLaw (a b : ℝ) : Measure ℝ :=
  if a = b then Measure.dirac a else intervalLaw (min a b) (max a b)

/-- Full measure equality, including reversed segments and constant coordinates. -/
theorem affineUniform_sorted (a b : ℝ) :
    (affineUniform a b : Measure ℝ) = sortedIntervalLaw a b := by
  rcases lt_trichotomy a b with h | h | h
  · simp only [sortedIntervalLaw, ne_of_lt h, ite_false, min_eq_left (le_of_lt h),
      max_eq_right (le_of_lt h)]
    exact affineUniform_increasing h
  · subst b
    simp only [sortedIntervalLaw, ite_true]
    exact affineUniform_constant a
  · simp only [sortedIntervalLaw, ne_of_gt h, ite_false, min_eq_right (le_of_lt h),
      max_eq_left (le_of_lt h)]
    exact affineUniform_decreasing h

theorem affineUniform_reverse (a b : ℝ) :
    (affineUniform a b : Measure ℝ) = (affineUniform b a : Measure ℝ) := by
  rw [affineUniform_sorted, affineUniform_sorted]
  by_cases h : a = b
  · subst b
    rfl
  · simp [sortedIntervalLaw, h, Ne.symm h, min_comm, max_comm]

theorem affineLine_between {a b t : ℝ} (hab : a ≤ b) (ht : 0 ≤ t ∧ t ≤ 1) :
    a ≤ affineLine a b t ∧ affineLine a b t ≤ b := by
  unfold affineLine
  have h1 := mul_nonneg ht.1 (sub_nonneg.mpr hab)
  have h2 := mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr hab)
  constructor <;> nlinarith

theorem unitUniform_supported :
    ∀ᵐ t ∂(unitUniform : Measure ℝ), t ∈ Icc 0 1 := by
  change ∀ᵐ t ∂uniformLaw 1, t ∈ Icc 0 1
  simpa [uniformLaw] using (ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Icc)

end Blotto
