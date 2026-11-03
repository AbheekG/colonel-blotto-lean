import Blotto.Mixed
import Mathlib.Probability.CDF

/-! Half ties and stability for arbitrary marginal probability measures.
Closed-CDF error implies strict-CDF error by taking left limits. -/

namespace Blotto

open MeasureTheory Set Filter ProbabilityTheory Function
open scoped Topology BigOperators

noncomputable def marginal {n : ℕ} (μ : Mixed n) (j : Fin n) : ProbabilityMeasure ℝ :=
  μ.map (fun x => x j)

noncomputable def closedCDF {n : ℕ} (μ : Mixed n) (j : Fin n) (t : ℝ) : ℝ :=
  (marginal μ j : Measure ℝ).real (Iic t)

noncomputable def strictCDF {n : ℕ} (μ : Mixed n) (j : Fin n) (t : ℝ) : ℝ :=
  (marginal μ j : Measure ℝ).real (Iio t)

def CDFClose {n : ℕ} (μ ν : Mixed n) (δ : ℝ) : Prop :=
  ∀ j t, |closedCDF μ j t - closedCDF ν j t| ≤ δ

theorem real_Iio_eq_leftLim (ρ : ProbabilityMeasure ℝ) (t : ℝ) :
    (ρ : Measure ℝ).real (Iio t) = leftLim (cdf (ρ : Measure ℝ)) t := by
  have hl : 0 ≤ leftLim (cdf (ρ : Measure ℝ)) t := by
    exact le_trans (cdf_nonneg _ (t - 1))
      ((monotone_cdf _).le_leftLim (by linarith : t - 1 < t))
  rw [measureReal_def]
  conv_lhs => rw [← measure_cdf (ρ : Measure ℝ)]
  rw [StieltjesFunction.measure_Iio _ (tendsto_cdf_atBot _), sub_zero,
    ENNReal.toReal_ofReal hl]

theorem strictCDF_close {n : ℕ} {μ ν : Mixed n} {δ : ℝ}
    (h : CDFClose μ ν δ) (j : Fin n) (t : ℝ) :
    |strictCDF μ j t - strictCDF ν j t| ≤ δ := by
  unfold strictCDF
  rw [real_Iio_eq_leftLim, real_Iio_eq_leftLim]
  apply le_of_tendsto
    (((monotone_cdf (marginal μ j : Measure ℝ)).tendsto_leftLim t).sub
      ((monotone_cdf (marginal ν j : Measure ℝ)).tendsto_leftLim t)).abs
  exact Eventually.of_forall fun s => by
    simpa [cdf_eq_real, closedCDF] using h j s

theorem share_indicator (s t : ℝ) :
    share s t = (1 / 2 : ℝ) *
      ((Iio s).indicator (fun _ => (1 : ℝ)) t +
        (Iic s).indicator (fun _ => (1 : ℝ)) t) := by
  rcases lt_trichotomy t s with h | h | h
  · norm_num [share, h, le_of_lt h]
  · subst t
    simp
  · simp [share, not_lt_of_ge (le_of_lt h), ne_of_lt h, not_le_of_gt h]

/-- The half-tie formula includes an atom at zero without an exception. -/
theorem integral_share (ρ : ProbabilityMeasure ℝ) (s : ℝ) :
    (∫ t, share s t ∂(ρ : Measure ℝ)) =
      ((ρ : Measure ℝ).real (Iio s) + (ρ : Measure ℝ).real (Iic s)) / 2 := by
  simp_rw [share_indicator]
  rw [integral_const_mul, integral_add
    ((integrable_const (1 : ℝ)).indicator measurableSet_Iio)
    ((integrable_const (1 : ℝ)).indicator measurableSet_Iic)]
  simp only [integral_indicator_const (1 : ℝ) measurableSet_Iio,
    integral_indicator_const (1 : ℝ) measurableSet_Iic, smul_eq_mul, mul_one]
  ring

theorem marginal_integral_share {n : ℕ} (μ : Mixed n) (j : Fin n) (s : ℝ) :
    (∫ x, share s (x j) ∂(μ : Measure (Allocation n))) =
      (strictCDF μ j s + closedCDF μ j s) / 2 := by
  unfold strictCDF closedCDF
  rw [← integral_share (marginal μ j)]
  exact (integral_map (μ := (μ : Measure (Allocation n)))
    (φ := fun x => x j) (f := fun t => share s t) (measurable_pi_apply j).aemeasurable
    ((measurable_share.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)).symm

theorem purePayoff_marginals {n : ℕ} (v : Values n) (x : Allocation n) (μ : Mixed n) :
    purePayoff v x μ = ∑ j, v.weight j * (strictCDF μ j (x j) + closedCDF μ j (x j)) / 2 := by
  unfold purePayoff payoff
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro j _
    rw [integral_const_mul, marginal_integral_share]
    ring
  · intro j _
    apply Integrable.const_mul
    apply (integrable_const (1 : ℝ)).mono'
    · exact ((measurable_share.comp
        (measurable_const.prodMk (measurable_pi_apply j))).aestronglyMeasurable)
    · exact Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (share_nonneg _ _)]
        exact share_le_one _ _

theorem halfCDF_close {n : ℕ} {μ ν : Mixed n} {δ : ℝ}
    (h : CDFClose μ ν δ) (j : Fin n) (s : ℝ) :
    |(strictCDF μ j s + closedCDF μ j s) / 2 -
      (strictCDF ν j s + closedCDF ν j s) / 2| ≤ δ := by
  have hs := (abs_le.mp (strictCDF_close h j s))
  have hw := (abs_le.mp (h j s))
  apply abs_le.mpr
  constructor <;> linarith

theorem purePayoff_close {n : ℕ} (v : Values n) {μ ν : Mixed n} {δ : ℝ}
    (h : CDFClose μ ν δ) (x : Allocation n) :
    |purePayoff v x μ - purePayoff v x ν| ≤ δ := by
  rw [purePayoff_marginals, purePayoff_marginals, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ j, |v.weight j * (strictCDF μ j (x j) + closedCDF μ j (x j)) / 2 -
        v.weight j * (strictCDF ν j (x j) + closedCDF ν j (x j)) / 2| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, v.weight j * δ := by
      apply Finset.sum_le_sum
      intro j _
      have hj := mul_le_mul_of_nonneg_left (halfCDF_close h j (x j)) (le_of_lt (v.positive j))
      rw [← abs_of_pos (v.positive j), ← abs_mul] at hj
      have he : v.weight j * (strictCDF μ j (x j) + closedCDF μ j (x j)) / 2 -
          v.weight j * (strictCDF ν j (x j) + closedCDF ν j (x j)) / 2 =
          v.weight j * ((strictCDF μ j (x j) + closedCDF μ j (x j)) / 2 -
            (strictCDF ν j (x j) + closedCDF ν j (x j)) / 2) := by ring
      rw [he]
      simpa only [abs_of_pos (v.positive j)] using hj
    _ = δ := by rw [← Finset.sum_mul, v.normalized, one_mul]

theorem expected_opponent_close {n : ℕ} (v : Values n) (μ : Mixed n)
    {ν ν' : Mixed n} {δ : ℝ} (h : CDFClose ν ν' δ) :
    |expected v μ ν - expected v μ ν'| ≤ δ := by
  rw [expected_iterated, expected_iterated, ← integral_sub
    (integrable_purePayoff v μ ν) (integrable_purePayoff v μ ν')]
  have hb := norm_integral_le_of_norm_le_const (μ := (μ : Measure (Allocation n)))
    (f := fun x => purePayoff v x ν - purePayoff v x ν') (C := δ)
    (Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs] using purePayoff_close v h x)
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using hb

theorem expected_own_close {n : ℕ} (v : Values n) {μ μ' : Mixed n}
    {δ : ℝ} (h : CDFClose μ μ' δ) (ν : Mixed n) :
    |expected v μ ν - expected v μ' ν| ≤ δ := by
  have hb := abs_le.mp (expected_opponent_close v ν h)
  have h1 := expected_constant_sum v μ ν
  have h2 := expected_constant_sum v μ' ν
  apply abs_le.mpr
  constructor <;> linarith

theorem expected_profile_close {n : ℕ} (v : Values n) {μ μ' ν ν' : Mixed n}
    {δA δB : ℝ} (hA : CDFClose μ μ' δA) (hB : CDFClose ν ν' δB) :
    |expected v μ ν - expected v μ' ν'| ≤ δA + δB := by
  have h1 := abs_le.mp (expected_own_close v hA ν)
  have h2 := abs_le.mp (expected_opponent_close v μ' hB)
  apply abs_le.mpr
  constructor <;> linarith

theorem security_close {n : ℕ} (v : Values n) {B δ : ℝ} (hB : 0 ≤ B)
    {ν ν' : Mixed n} (h : CDFClose ν ν' δ) :
    |security v B ν - security v B ν'| ≤ δ := by
  have h1 : security v B ν ≤ security v B ν' + δ := by
    apply security_le v hB ν
    intro x hx
    have hc := abs_le.mp (purePayoff_close v h x)
    have hs := purePayoff_le_security v hx ν'
    linarith
  have h2 : security v B ν' ≤ security v B ν + δ := by
    apply security_le v hB ν'
    intro x hx
    have hc := abs_le.mp (purePayoff_close v h x)
    have hs := purePayoff_le_security v hx ν
    linarith
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Manuscript Lemma 1.1, for a player's own positive value row.
No equilibrium, continuity, or feasibility of separately supplied marginals is assumed. -/
theorem regret_stability {n : ℕ} (v : Values n) {B δA δB : ℝ} (hBudget : 0 ≤ B)
    {μ μ' ν ν' : Mixed n} (hA : CDFClose μ μ' δA) (hB : CDFClose ν ν' δB) :
    regret v B μ' ν' ≤ regret v B μ ν + δA + 2 * δB := by
  have hs := abs_le.mp (security_close v hBudget hB)
  have he := abs_le.mp (expected_profile_close v hA hB)
  unfold regret
  linarith

/-- The two inequalities also hold with different player value rows. -/
theorem both_regrets_stability {n : ℕ} (vA vB : Values n) {A B δA δB : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) {μ μ' ν ν' : Mixed n}
    (hcA : CDFClose μ μ' δA) (hcB : CDFClose ν ν' δB) :
    regret vA A μ' ν' ≤ regret vA A μ ν + δA + 2 * δB ∧
    regret vB B ν' μ' ≤ regret vB B ν μ + δB + 2 * δA :=
  ⟨regret_stability vA hA hcA hcB, regret_stability vB hB hcB hcA⟩

end Blotto
