import Blotto.SparseMWEntropyEndpoints

/-! Sharp one-half second-moment entropy bound for nonnegative effective
losses, exactly the sign used by the actual rounded sparse learner in R135 §3
and R136 §1. Signed auxiliary-noise Hoeffding bounds remain separate. -/

namespace Blotto
open scoped BigOperators Classical
namespace SparseMW

theorem exp_neg_quadratic_sharp (z : ℝ) (hz : 0 ≤ z) :
    Real.exp (-z) ≤ 1 - z + z ^ 2 / 2 := by
  let q := 1 - z + z ^ 2 / 2
  have hq : 0 ≤ q := by dsimp [q]; nlinarith [sq_nonneg (z - 1)]
  have hpartial := Real.sum_le_exp_of_nonneg hz 5
  norm_num [Finset.sum_range_succ] at hpartial
  have hmul := mul_le_mul_of_nonneg_left hpartial hq
  have h3 : 0 ≤ z ^ 3 := pow_nonneg hz _
  have h4 : 0 ≤ z ^ 4 := pow_nonneg hz _
  have h5 : 0 ≤ z ^ 5 := pow_nonneg hz _
  have h6 : 0 ≤ z ^ 6 := pow_nonneg hz _
  have hpoly : 1 ≤ q * (1 + z + z ^ 2 / 2 + z ^ 3 / 6 + z ^ 4 / 24) := by
    have he : q * (1 + z + z ^ 2 / 2 + z ^ 3 / 6 + z ^ 4 / 24) =
        1 + z ^ 3 / 6 + z ^ 4 / 8 + z ^ 5 / 24 + z ^ 6 / 48 := by dsimp [q]; ring
    rw [he]
    linarith
  have he : 1 ≤ q * Real.exp z := hpoly.trans (by convert hmul using 1)
  rw [Real.exp_neg]
  have hb : 1 / Real.exp z ≤ q := (div_le_iff₀ (Real.exp_pos z)).mpr he
  simpa only [one_div, q] using hb

theorem log_normalizer_sharp {n : ℕ} (probability loss : Fin n → ℝ) (eta : ℝ)
    (hp : ∀ i, 0 < probability i) (hs : ∑ i, probability i = 1)
    (heta : 0 ≤ eta) (hl : ∀ i, 0 ≤ loss i) :
    Real.log (normalizer probability loss eta) ≤
      -eta * (∑ i, probability i * loss i) +
        (eta ^ 2 / 2) * (∑ i, probability i * loss i ^ 2) := by
  have hlog := Real.log_le_sub_one_of_pos (normalizer_positive probability loss eta hp hs)
  have hsum : normalizer probability loss eta ≤
      1 - eta * (∑ i, probability i * loss i) +
        (eta ^ 2 / 2) * (∑ i, probability i * loss i ^ 2) := by
    calc
      _ ≤ ∑ i, probability i * (1 - eta * loss i + (eta * loss i) ^ 2 / 2) := by
        apply Finset.sum_le_sum
        intro i _
        have he := exp_neg_quadratic_sharp (eta * loss i) (mul_nonneg heta (hl i))
        simpa only [neg_mul] using mul_le_mul_of_nonneg_left he (hp i).le
      _ = _ := by
        simp only [mul_add, mul_sub, mul_one, Finset.sum_add_distrib, Finset.sum_sub_distrib]
        rw [hs]
        have hlinear : (∑ i, probability i * (eta * loss i)) = eta * ∑ i, probability i * loss i := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
        have hquad : (∑ i, probability i * ((eta * loss i) ^ 2 / 2)) =
            (eta ^ 2 / 2) * ∑ i, probability i * loss i ^ 2 := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
        rw [hlinear, hquad]
  linarith

theorem relativeEntropy_step_sharp {n : ℕ} (comparator probability loss : Fin n → ℝ) (eta : ℝ)
    (hp : ∀ i, 0 < probability i) (hs : ∑ i, probability i = 1)
    (hu : ∑ i, comparator i = 1) (heta : 0 ≤ eta) (hl : ∀ i, 0 ≤ loss i) :
    eta * (∑ i, (probability i - comparator i) * loss i) ≤
      relativeEntropy comparator probability - relativeEntropy comparator (normalizedUpdate probability loss eta) +
        (eta ^ 2 / 2) * (∑ i, probability i * loss i ^ 2) := by
  have he := relativeEntropy_step_identity comparator probability loss eta hp hs hu
  have hb := log_normalizer_sharp probability loss eta hp hs heta hl
  have hsum : (∑ i, (probability i - comparator i) * loss i) =
      (∑ i, probability i * loss i) - ∑ i, comparator i * loss i := by
    simp only [sub_mul, Finset.sum_sub_distrib]
  rw [hsum]
  linarith

theorem finite_sharp_regret {n : ℕ} (comparator : Fin n → ℝ)
    (probability loss : ℕ → Fin n → ℝ) (eta : ℝ)
    (hu : ∀ i, 0 ≤ comparator i) (hsu : ∑ i, comparator i = 1)
    (hp : ∀ t i, 0 < probability t i) (hs : ∀ t, ∑ i, probability t i = 1)
    (heta : 0 ≤ eta) (hl : ∀ t i, 0 ≤ loss t i)
    (hstep : ∀ t, probability (t + 1) = normalizedUpdate (probability t) (loss t) eta)
    (T : ℕ) :
    eta * (∑ t ∈ Finset.range T, ∑ i, (probability t i - comparator i) * loss t i) ≤
      relativeEntropy comparator (probability 0) + (eta ^ 2 / 2) *
        (∑ t ∈ Finset.range T, ∑ i, probability t i * loss t i ^ 2) := by
  have htelescope : ∀ T : ℕ,
      eta * (∑ t ∈ Finset.range T, ∑ i, (probability t i - comparator i) * loss t i) ≤
        relativeEntropy comparator (probability 0) - relativeEntropy comparator (probability T) +
          (eta ^ 2 / 2) * (∑ t ∈ Finset.range T, ∑ i, probability t i * loss t i ^ 2) := by
    intro T
    induction T with
    | zero => simp
    | succ T ih =>
      have he := relativeEntropy_step_sharp comparator (probability T) (loss T) eta
        (hp T) (hs T) hsu heta (hl T)
      rw [← hstep T] at he
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      nlinarith
  have he := htelescope T
  have hn := relativeEntropy_nonnegative comparator (probability T) hu hsu (hp T) (hs T)
  linarith

theorem finite_uniform_sharp_regret {n : ℕ} (hn : 0 < n) (comparator : Fin n → ℝ)
    (probability loss : ℕ → Fin n → ℝ) (eta : ℝ)
    (hu : ∀ i, 0 ≤ comparator i) (hsu : ∑ i, comparator i = 1)
    (hp : ∀ t i, 0 < probability t i) (hs : ∀ t, ∑ i, probability t i = 1)
    (hstart : probability 0 = fun _ => 1 / (n : ℝ))
    (heta : 0 ≤ eta) (hl : ∀ t i, 0 ≤ loss t i)
    (hstep : ∀ t, probability (t + 1) = normalizedUpdate (probability t) (loss t) eta)
    (T : ℕ) :
    eta * (∑ t ∈ Finset.range T, ∑ i, (probability t i - comparator i) * loss t i) ≤
      Real.log n + (eta ^ 2 / 2) * (∑ t ∈ Finset.range T, ∑ i, probability t i * loss t i ^ 2) := by
  have he := finite_sharp_regret comparator probability loss eta hu hsu hp hs heta hl hstep T
  rw [hstart] at he
  have hb := relativeEntropy_uniform_bound hn comparator hu hsu
  linarith

theorem finite_uniform_bounded_sharp_regret {n : ℕ} (hn : 0 < n) (comparator : Fin n → ℝ)
    (probability loss : ℕ → Fin n → ℝ) (eta cap : ℝ)
    (hu : ∀ i, 0 ≤ comparator i) (hsu : ∑ i, comparator i = 1)
    (hp : ∀ t i, 0 < probability t i) (hs : ∀ t, ∑ i, probability t i = 1)
    (hstart : probability 0 = fun _ => 1 / (n : ℝ))
    (heta : 0 ≤ eta) (hcap : 0 ≤ cap) (hl : ∀ t i, 0 ≤ loss t i ∧ loss t i ≤ cap)
    (hstep : ∀ t, probability (t + 1) = normalizedUpdate (probability t) (loss t) eta)
    (T : ℕ) :
    eta * (∑ t ∈ Finset.range T, ∑ i, (probability t i - comparator i) * loss t i) ≤
      Real.log n + (eta ^ 2 / 2) * (T : ℝ) * cap ^ 2 := by
  have he := finite_uniform_sharp_regret hn comparator probability loss eta hu hsu hp hs hstart
    heta (fun t i => (hl t i).1) hstep T
  have hmoment : (∑ t ∈ Finset.range T, ∑ i, probability t i * loss t i ^ 2) ≤ (T : ℝ) * cap ^ 2 := by
    calc
      _ ≤ ∑ t ∈ Finset.range T, cap ^ 2 := by
        apply Finset.sum_le_sum
        intro t _
        calc
          _ ≤ ∑ i, probability t i * cap ^ 2 := by
            apply Finset.sum_le_sum
            intro i _
            have hb : loss t i ^ 2 ≤ cap ^ 2 := by nlinarith [(hl t i).1, (hl t i).2]
            exact mul_le_mul_of_nonneg_left hb (hp t i).le
          _ = cap ^ 2 := by rw [← Finset.sum_mul, hs t, one_mul]
      _ = _ := by simp
  have hmul := mul_le_mul_of_nonneg_left hmoment (by positivity : 0 ≤ eta ^ 2 / 2)
  nlinarith

theorem rounded_effectiveLoss_nonnegative {eta multiplier : ℝ} (heta : 0 < eta)
    (hm : 0 < multiplier) (hupper : multiplier ≤ 1) : 0 ≤ effectiveLoss eta multiplier := by
  have hlog := Real.log_le_log hm hupper
  rw [Real.log_one] at hlog
  exact div_nonneg (by linarith) heta.le

end SparseMW
end Blotto
