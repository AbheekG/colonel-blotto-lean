import Blotto.SparseMWEntropy

/-! Comparator endpoint bounds for the finite relative entropy used by the
rounded sparse-MW process. Zero comparator weights are retained explicitly. -/

namespace Blotto
open scoped BigOperators Classical
namespace SparseMW

theorem relativeEntropy_nonnegative {n : ℕ} (comparator probability : Fin n → ℝ)
    (hu : ∀ i, 0 ≤ comparator i) (hsu : ∑ i, comparator i = 1)
    (hp : ∀ i, 0 < probability i) (hsp : ∑ i, probability i = 1) :
    0 ≤ relativeEntropy comparator probability := by
  have hpoint : ∀ i, comparator i - probability i ≤
      comparator i * (Real.log (comparator i) - Real.log (probability i)) := by
    intro i
    by_cases hz : comparator i = 0
    · simp only [hz, zero_sub, zero_mul]
      linarith [hp i]
    · have hi : 0 < comparator i := lt_of_le_of_ne (hu i) (Ne.symm hz)
      have he := Real.log_le_sub_one_of_pos (div_pos (hp i) hi)
      rw [Real.log_div (ne_of_gt (hp i)) (ne_of_gt hi)] at he
      have hm := mul_le_mul_of_nonneg_left he hi.le
      have hcancel : comparator i * (probability i / comparator i - 1) = probability i - comparator i := by
        field_simp
      rw [hcancel] at hm
      nlinarith
  have hs : (∑ i : Fin n, (comparator i - probability i)) ≤
      (∑ i : Fin n, comparator i * (Real.log (comparator i) - Real.log (probability i))) :=
    Finset.sum_le_sum (fun i _ => hpoint i)
  simp only [Finset.sum_sub_distrib, hsu, hsp, sub_self] at hs
  exact hs

theorem comparator_coordinate_le_one {n : ℕ} (comparator : Fin n → ℝ)
    (hu : ∀ i, 0 ≤ comparator i) (hsu : ∑ i, comparator i = 1) (i : Fin n) :
    comparator i ≤ 1 := by
  have he := Finset.single_le_sum (fun j _ => hu j) (Finset.mem_univ i)
  rw [hsu] at he
  exact he

theorem relativeEntropy_prior_lower_bound {n : ℕ} (comparator probability : Fin n → ℝ)
    (hu : ∀ i, 0 ≤ comparator i) (hsu : ∑ i, comparator i = 1)
    (minimum : ℝ) (hmin : 0 < minimum) (hp : ∀ i, minimum ≤ probability i) :
    relativeEntropy comparator probability ≤ -Real.log minimum := by
  have hpoint : ∀ i, comparator i * (Real.log (comparator i) - Real.log (probability i)) ≤
      comparator i * (-Real.log minimum) := by
    intro i
    by_cases hz : comparator i = 0
    · simp only [hz, zero_mul, le_refl]
    · have hi : 0 < comparator i := lt_of_le_of_ne (hu i) (Ne.symm hz)
      have hle := comparator_coordinate_le_one comparator hu hsu i
      have hc := Real.log_le_log hi hle
      rw [Real.log_one] at hc
      have hpLog := Real.log_le_log hmin (hp i)
      exact mul_le_mul_of_nonneg_left (by linarith) (hu i)
  calc
    relativeEntropy comparator probability ≤ ∑ i, comparator i * (-Real.log minimum) :=
      Finset.sum_le_sum (fun i _ => hpoint i)
    _ = -Real.log minimum := by rw [← Finset.sum_mul, hsu, one_mul]

theorem relativeEntropy_uniform_bound {n : ℕ} (hn : 0 < n) (comparator : Fin n → ℝ)
    (hu : ∀ i, 0 ≤ comparator i) (hsu : ∑ i, comparator i = 1) :
    relativeEntropy comparator (fun _ => 1 / (n : ℝ)) ≤ Real.log n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have he := relativeEntropy_prior_lower_bound comparator (fun _ => 1 / (n : ℝ)) hu hsu
    (1 / (n : ℝ)) (by positivity) (fun _ => le_rfl)
  have hlog : -Real.log (1 / (n : ℝ)) = Real.log n := by
    rw [Real.log_div (by norm_num) (ne_of_gt hnR), Real.log_one]
    ring
  rw [hlog] at he
  exact he

theorem finite_relativeEntropy_regret_endpoint {n : ℕ} (comparator : Fin n → ℝ)
    (probability loss : ℕ → Fin n → ℝ) (eta : ℝ)
    (hu : ∀ i, 0 ≤ comparator i) (hsu : ∑ i, comparator i = 1)
    (hp : ∀ t i, 0 < probability t i) (hs : ∀ t, ∑ i, probability t i = 1)
    (hscaled : ∀ t i, |eta * loss t i| ≤ 1)
    (hstep : ∀ t, probability (t + 1) = normalizedUpdate (probability t) (loss t) eta)
    (T : ℕ) :
    eta * (∑ t ∈ Finset.range T, ∑ i, (probability t i - comparator i) * loss t i) ≤
      relativeEntropy comparator (probability 0) + (3 / 4 : ℝ) * eta ^ 2 *
        (∑ t ∈ Finset.range T, ∑ i, probability t i * loss t i ^ 2) := by
  have he := finite_relativeEntropy_regret comparator probability loss eta hsu hp hs hscaled hstep T
  have hn := relativeEntropy_nonnegative comparator (probability T) hu hsu (hp T) (hs T)
  linarith

end SparseMW
end Blotto
