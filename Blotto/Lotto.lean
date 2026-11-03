import Blotto.CDF
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! The incentive part of manuscript §2.1.1, conditional on feasible
whole-allocation couplings of the specified actual marginal measures.
This file does not assume or claim existence of those couplings. -/

namespace Blotto

open MeasureTheory Set Filter
open scoped BigOperators

noncomputable def uniformLaw (ℓ : ℝ) : Measure ℝ :=
  (ENNReal.ofReal ℓ)⁻¹ • volume.restrict (Icc 0 ℓ)

noncomputable def uniformMarginal (ℓ : ℝ) (hℓ : 0 < ℓ) : ProbabilityMeasure ℝ :=
  ⟨uniformLaw ℓ, by
    constructor
    simp only [uniformLaw, Measure.smul_apply, Measure.restrict_apply_univ,
      Real.volume_Icc, sub_zero, smul_eq_mul]
    exact ENNReal.inv_mul_cancel (ne_of_gt (ENNReal.ofReal_pos.mpr hℓ)) ENNReal.ofReal_ne_top⟩

noncomputable def zeroUniformLaw (ℓ b : ℝ) : Measure ℝ :=
  ENNReal.ofReal (1 - b) • Measure.dirac 0 + ENNReal.ofReal b • uniformLaw ℓ

theorem uniform_closedCDF (ℓ : ℝ) (hℓ : 0 < ℓ) (s : ℝ) :
    (uniformMarginal ℓ hℓ : Measure ℝ).real (Iic s) = max (min s ℓ) 0 / ℓ := by
  have hi : Iic s ∩ Icc 0 ℓ = Icc 0 (min s ℓ) := by
    ext t
    simp only [mem_inter_iff, mem_Iic, mem_Icc, le_min_iff]
    tauto
  change (uniformLaw ℓ).real (Iic s) = _
  rw [uniformLaw, measureReal_ennreal_smul_apply]
  simp only [measureReal_def, Measure.restrict_apply measurableSet_Iic, hi,
    Real.volume_Icc, sub_zero, ENNReal.toReal_inv, ENNReal.toReal_ofReal (le_of_lt hℓ),
    ENNReal.toReal_ofReal']
  ring

theorem uniform_singleton (ℓ : ℝ) (s : ℝ) : uniformLaw ℓ {s} = 0 := by
  have hz : volume ({s} ∩ Icc 0 ℓ) = 0 := by
    apply le_antisymm _ zero_le
    calc
      volume ({s} ∩ Icc 0 ℓ) ≤ volume {s} := measure_mono inter_subset_left
      _ = 0 := measure_singleton s
  simp [uniformLaw, Measure.restrict_apply (measurableSet_singleton s), hz]

theorem uniform_integral_share (ℓ : ℝ) (hℓ : 0 < ℓ) (s : ℝ) :
    (∫ t, share s t ∂uniformLaw ℓ) = max (min s ℓ) 0 / ℓ := by
  change (∫ t, share s t ∂(uniformMarginal ℓ hℓ : Measure ℝ)) = _
  rw [integral_share (uniformMarginal ℓ hℓ)]
  have he : (uniformMarginal ℓ hℓ : Measure ℝ).real (Iio s) =
      (uniformMarginal ℓ hℓ : Measure ℝ).real (Iic s) := by
    unfold Measure.real
    congr 1
    exact measure_congr (Iio_ae_eq_Iic' (uniform_singleton ℓ s))
  rw [he, uniform_closedCDF]
  ring

theorem uniform_share_upper (ℓ : ℝ) (hℓ : 0 < ℓ) {s : ℝ} (hs : 0 ≤ s) :
    (∫ t, share s t ∂uniformLaw ℓ) ≤ s / ℓ := by
  rw [uniform_integral_share ℓ hℓ]
  exact div_le_div_of_nonneg_right (max_le (min_le_left _ _) hs) (le_of_lt hℓ)

theorem integrable_share_measure (ρ : Measure ℝ) [IsFiniteMeasure ρ] (s : ℝ) :
    Integrable (fun t => share s t) ρ := by
  apply (integrable_const (1 : ℝ)).mono'
  · exact (measurable_share.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  · exact Eventually.of_forall fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg (share_nonneg _ _)]
      exact share_le_one _ _

theorem zeroUniform_integral_share (ℓ : ℝ) (hℓ : 0 < ℓ) {b : ℝ}
    (hb : 0 ≤ b) (hb1 : b ≤ 1) (s : ℝ) :
    (∫ t, share s t ∂zeroUniformLaw ℓ b) =
      (1 - b) * share s 0 + b * (max (min s ℓ) 0 / ℓ) := by
  let : IsProbabilityMeasure (uniformLaw ℓ) := (uniformMarginal ℓ hℓ).property
  unfold zeroUniformLaw
  rw [integral_add_measure
    ((integrable_share_measure (Measure.dirac 0) s).smul_measure ENNReal.ofReal_ne_top)
    ((integrable_share_measure (uniformLaw ℓ) s).smul_measure ENNReal.ofReal_ne_top),
    integral_smul_measure, integral_smul_measure, integral_dirac,
    uniform_integral_share ℓ hℓ]
  simp [ENNReal.toReal_ofReal hb, ENNReal.toReal_ofReal (sub_nonneg.mpr hb1)]

theorem zeroUniform_share_upper (ℓ : ℝ) (hℓ : 0 < ℓ) {b s : ℝ}
    (hb : 0 ≤ b) (hb1 : b ≤ 1) (hs : 0 ≤ s) :
    (∫ t, share s t ∂zeroUniformLaw ℓ b) ≤ 1 - b + b * (s / ℓ) := by
  rw [zeroUniform_integral_share ℓ hℓ hb hb1]
  have h1 := mul_le_mul_of_nonneg_left (share_le_one s 0) (sub_nonneg.mpr hb1)
  have h2 := mul_le_mul_of_nonneg_left (uniform_share_upper ℓ hℓ hs) hb
  rw [uniform_integral_share ℓ hℓ] at h2
  linarith

theorem zeroUniform_zero_tie (ℓ : ℝ) (hℓ : 0 < ℓ) {b : ℝ}
    (hb : 0 ≤ b) (hb1 : b ≤ 1) :
    (∫ t, share 0 t ∂zeroUniformLaw ℓ b) = (1 - b) / 2 := by
  rw [zeroUniform_integral_share ℓ hℓ hb hb1]
  simp [min_eq_left (le_of_lt hℓ)]
  ring

theorem purePayoff_marginal_integrals {n : ℕ} (v : Values n)
    (x : Allocation n) (μ : Mixed n) :
    purePayoff v x μ = ∑ j, v.weight j *
      (∫ t, share (x j) t ∂(marginal μ j : Measure ℝ)) := by
  rw [purePayoff_marginals]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_share]
  unfold strictCDF closedCDF
  ring

theorem uniform_security {n : ℕ} (v : Values n) {B : ℝ} (hB : 0 ≤ B)
    (μ : Mixed n) (hμ : ∀ j, (marginal μ j : Measure ℝ) = uniformLaw (2 * v.weight j)) :
    security v B μ ≤ B / 2 := by
  apply security_le v hB μ
  intro x hx
  rw [purePayoff_marginal_integrals]
  calc
    _ ≤ ∑ j, x j / 2 := by
      apply Finset.sum_le_sum
      intro j _
      rw [hμ j]
      have hv := v.positive j
      have hj := mul_le_mul_of_nonneg_left
        (uniform_share_upper (2 * v.weight j) (by positivity) (hx.1 j))
        (le_of_lt (v.positive j))
      convert hj using 1
      field_simp [ne_of_gt hv]
    _ = (∑ j, x j) / 2 := by rw [Finset.sum_div]
    _ ≤ B / 2 := div_le_div_of_nonneg_right hx.2 (by norm_num)

theorem zeroUniform_security {n : ℕ} (v : Values n) {b : ℝ}
    (hb : 0 ≤ b) (hb1 : b ≤ 1) (ν : Mixed n)
    (hν : ∀ j, (marginal ν j : Measure ℝ) = zeroUniformLaw (2 * v.weight j) b) :
    security v 1 ν ≤ 1 - b / 2 := by
  apply security_le v (by norm_num) ν
  intro x hx
  rw [purePayoff_marginal_integrals]
  calc
    _ ≤ ∑ j, (v.weight j * (1 - b) + b * x j / 2) := by
      apply Finset.sum_le_sum
      intro j _
      rw [hν j]
      have hv := v.positive j
      have hj := mul_le_mul_of_nonneg_left
        (zeroUniform_share_upper (2 * v.weight j) (by positivity) hb hb1 (hx.1 j))
        (le_of_lt (v.positive j))
      convert hj using 1
      field_simp [ne_of_gt hv]
    _ = 1 - b + b * (∑ j, x j) / 2 := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_div,
        ← Finset.mul_sum, v.normalized, one_mul]
    _ ≤ 1 - b / 2 := by nlinarith [hx.2]

/-- Feasible couplings of the actual Lotto laws are exact Nash, with the
claimed payoffs. The coupling existence and sampler proofs remain separate. -/
theorem feasible_lotto_couplings_equilibrium {n : ℕ} (v : Values n) {b : ℝ}
    (hb : 0 < b) (hb1 : b ≤ 1) (μ ν : Mixed n)
    (hsμ : Supported 1 μ) (hsν : Supported b ν)
    (hμ : ∀ j, (marginal μ j : Measure ℝ) = uniformLaw (2 * v.weight j))
    (hν : ∀ j, (marginal ν j : Measure ℝ) = zeroUniformLaw (2 * v.weight j) b) :
    regret v 1 μ ν = 0 ∧ regret v b ν μ = 0 ∧
      expected v μ ν = 1 - b / 2 ∧ expected v ν μ = b / 2 := by
  have hA := zeroUniform_security v (le_of_lt hb) hb1 ν hν
  have hB := uniform_security v (le_of_lt hb) μ hμ
  have hr := regrets_le_of_security_sum v μ ν hsμ hsν (ε := 0) (by linarith)
  have hnA := regret_nonneg v μ ν hsμ
  have hnB := regret_nonneg v ν μ hsν
  have heA := expected_le_security v μ ν hsμ
  have heB := expected_le_security v ν μ hsν
  have he := expected_constant_sum v μ ν
  exact ⟨le_antisymm hr.1 hnA, le_antisymm hr.2 hnB, by linarith, by linarith⟩

end Blotto
