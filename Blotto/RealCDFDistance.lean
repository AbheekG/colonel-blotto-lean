import Blotto.FiniteMixture

/-! Kolmogorov distance of actual scalar probability laws. Affine transport
(including reflection and constant coordinates) and exact finite mixtures
preserve the stated discrepancy, including at atoms through left limits. -/

namespace Blotto
open MeasureTheory Set Filter ProbabilityTheory Function
open scoped Topology BigOperators

def RealCDFClose (ρ σ : ProbabilityMeasure ℝ) (δ : ℝ) : Prop :=
  ∀ z, |(ρ : Measure ℝ).real (Iic z) - (σ : Measure ℝ).real (Iic z)| ≤ δ

namespace RealCDFClose

theorem nonnegative {ρ σ : ProbabilityMeasure ℝ} {δ : ℝ} (h : RealCDFClose ρ σ δ) : 0 ≤ δ :=
  (abs_nonneg _).trans (h 0)

theorem symm {ρ σ : ProbabilityMeasure ℝ} {δ : ℝ} (h : RealCDFClose ρ σ δ) : RealCDFClose σ ρ δ := by
  intro z
  rw [abs_sub_comm]
  exact h z

theorem triangle {ρ σ τ : ProbabilityMeasure ℝ} {δ η : ℝ}
    (h : RealCDFClose ρ σ δ) (g : RealCDFClose σ τ η) : RealCDFClose ρ τ (δ + η) := by
  intro z
  calc
    _ ≤ |(ρ : Measure ℝ).real (Iic z) - (σ : Measure ℝ).real (Iic z)| +
        |(σ : Measure ℝ).real (Iic z) - (τ : Measure ℝ).real (Iic z)| := abs_sub_le _ _ _
    _ ≤ δ + η := add_le_add (h z) (g z)

theorem strict {ρ σ : ProbabilityMeasure ℝ} {δ : ℝ} (h : RealCDFClose ρ σ δ) (z : ℝ) :
    |(ρ : Measure ℝ).real (Iio z) - (σ : Measure ℝ).real (Iio z)| ≤ δ := by
  rw [real_Iio_eq_leftLim, real_Iio_eq_leftLim]
  apply le_of_tendsto
    (((monotone_cdf (ρ : Measure ℝ)).tendsto_leftLim z).sub
      ((monotone_cdf (σ : Measure ℝ)).tendsto_leftLim z)).abs
  exact Eventually.of_forall fun x => by simpa only [cdf_eq_real] using h x

theorem upper {ρ σ : ProbabilityMeasure ℝ} {δ : ℝ} (h : RealCDFClose ρ σ δ) (z : ℝ) :
    |(ρ : Measure ℝ).real (Ici z) - (σ : Measure ℝ).real (Ici z)| ≤ δ := by
  have he : Ici z = (Iio z)ᶜ := by ext x; simp
  rw [he, measureReal_compl measurableSet_Iio, measureReal_compl measurableSet_Iio, probReal_univ, probReal_univ]
  have heq : (1 - (ρ : Measure ℝ).real (Iio z)) - (1 - (σ : Measure ℝ).real (Iio z)) =
      (σ : Measure ℝ).real (Iio z) - (ρ : Measure ℝ).real (Iio z) := by ring
  rw [heq, abs_sub_comm]
  exact h.strict z

theorem affine {ρ σ : ProbabilityMeasure ℝ} {δ : ℝ} (h : RealCDFClose ρ σ δ) (a b : ℝ) :
    RealCDFClose (ρ.map (affineLine a b)) (σ.map (affineLine a b)) δ := by
  intro z
  rcases lt_trichotomy a b with hab | hab | hba
  · have hd := sub_pos.mpr hab
    have he : affineLine a b ⁻¹' Iic z = Iic ((z - a) / (b - a)) := by
      ext x
      simp only [mem_preimage, mem_Iic]
      rw [le_div_iff₀ hd]
      unfold affineLine
      constructor <;> intro hx <;> nlinarith
    change |(Measure.map (affineLine a b) (ρ : Measure ℝ)).real (Iic z) -
      (Measure.map (affineLine a b) (σ : Measure ℝ)).real (Iic z)| ≤ δ
    rw [map_measureReal_apply (measurable_affineLine a b) measurableSet_Iic,
      map_measureReal_apply (measurable_affineLine a b) measurableSet_Iic, he]
    exact h _
  · subst b
    have hf : affineLine a a = fun _ => a := by funext x; unfold affineLine; ring
    change |(Measure.map (affineLine a a) (ρ : Measure ℝ)).real (Iic z) -
      (Measure.map (affineLine a a) (σ : Measure ℝ)).real (Iic z)| ≤ δ
    rw [hf, Measure.map_const, Measure.map_const, measure_univ, measure_univ, one_smul]
    simpa only [sub_self, abs_zero] using h.nonnegative
  · have hd := sub_pos.mpr hba
    have he : affineLine a b ⁻¹' Iic z = Ici ((a - z) / (a - b)) := by
      ext x
      simp only [mem_preimage, mem_Iic, mem_Ici]
      rw [div_le_iff₀ hd]
      unfold affineLine
      constructor <;> intro hx <;> nlinarith
    change |(Measure.map (affineLine a b) (ρ : Measure ℝ)).real (Iic z) -
      (Measure.map (affineLine a b) (σ : Measure ℝ)).real (Iic z)| ≤ δ
    rw [map_measureReal_apply (measurable_affineLine a b) measurableSet_Iic,
      map_measureReal_apply (measurable_affineLine a b) measurableSet_Iic, he]
    exact h.upper _

end RealCDFClose

theorem probabilityMixture_real_apply {α : Type*} [MeasurableSpace α] {k : ℕ}
    (weight : Fin k → ℝ) (law : Fin k → ProbabilityMeasure α)
    (hw : ∀ i, 0 ≤ weight i) (hs : ∑ i, weight i = 1) (A : Set α) (hA : MeasurableSet A) :
    (probabilityMixture weight law hw hs : Measure α).real A =
      ∑ i, weight i * (law i : Measure α).real A := by
  change (Measure.sum (fun i => ENNReal.ofReal (weight i) • (law i : Measure α))).real A = _
  unfold Measure.real
  rw [Measure.sum_apply _ hA, tsum_fintype, ENNReal.toReal_sum (fun i _ => by
    rw [Measure.smul_apply]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ A))]
  apply Finset.sum_congr rfl
  intro i _
  rw [Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (hw i)]

theorem mixture_RealCDFClose {k : ℕ} (weight : Fin k → ℝ) (ρ σ : Fin k → ProbabilityMeasure ℝ)
    (hw : ∀ i, 0 ≤ weight i) (hs : ∑ i, weight i = 1) (δ : Fin k → ℝ)
    (h : ∀ i, RealCDFClose (ρ i) (σ i) (δ i)) :
    RealCDFClose (probabilityMixture weight ρ hw hs) (probabilityMixture weight σ hw hs) (∑ i, weight i * δ i) := by
  intro z
  rw [probabilityMixture_real_apply _ _ _ _ _ measurableSet_Iic,
    probabilityMixture_real_apply _ _ _ _ _ measurableSet_Iic, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, |weight i * (ρ i : Measure ℝ).real (Iic z) - weight i * (σ i : Measure ℝ).real (Iic z)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, weight i * δ i := by
      apply Finset.sum_le_sum
      intro i _
      rw [← mul_sub, abs_mul, abs_of_nonneg (hw i)]
      exact mul_le_mul_of_nonneg_left (h i z) (hw i)

theorem mixture_RealCDFClose_constant {k : ℕ} (weight : Fin k → ℝ) (ρ σ : Fin k → ProbabilityMeasure ℝ)
    (hw : ∀ i, 0 ≤ weight i) (hs : ∑ i, weight i = 1) {δ : ℝ}
    (h : ∀ i, RealCDFClose (ρ i) (σ i) δ) :
    RealCDFClose (probabilityMixture weight ρ hw hs) (probabilityMixture weight σ hw hs) δ := by
  have he := mixture_RealCDFClose weight ρ σ hw hs (fun _ => δ) h
  simpa only [← Finset.sum_mul, hs, one_mul] using he

end Blotto
