import Blotto.AdaptiveStochasticRegret

/-! Actual rounded rational history weights supply the pathwise learner
inequality used with the constructed auxiliary process. The remaining join is
from native product sampling to these transition laws and the saddle objective. -/

namespace Blotto
open scoped BigOperators Classical
namespace SparseMW

def computedHistoryMultipliers {a n : ℕ}
    (loss : List (Fin a) → Fin a → Fin n → ℚ) (eta theta : ℚ) : List (Fin a) → Fin a → Fin n → ℚ :=
  fun h x i => expMultiplierNative (eta * loss h x i) theta

theorem cumulative_perturbation {a n : ℕ}
    (loss effective : List (Fin a) → Fin a → Fin n → ℝ)
    (probability : List (Fin a) → Fin n → ℝ) (comparator : Fin n → ℝ) (error : ℝ)
    (hp : ∀ h i, 0 ≤ probability h i) (hs : ∀ h, ∑ i, probability h i = 1)
    (hu : ∀ i, 0 ≤ comparator i) (hsu : ∑ i, comparator i = 1)
    (hl : ∀ h x i, loss h x i ≤ effective h x i ∧ effective h x i ≤ loss h x i + error)
    (past : List (Fin a)) :
    cumulativePairing loss probability comparator past ≤
      cumulativePairing effective probability comparator past + past.length * error := by
  induction past with
  | nil => simp [cumulativePairing]
  | cons x past ih =>
    have he := computed_regret_comparison (probability past) comparator (loss past x) (effective past x)
      error (hp past) (hs past) hu hsu (hl past x)
    have hloss : (∑ i, loss past x i * (probability past i - comparator i)) =
        ∑ i, (probability past i - comparator i) * loss past x i := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    have heff : (∑ i, effective past x i * (probability past i - comparator i)) =
        ∑ i, (probability past i - comparator i) * effective past x i := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [cumulativePairing, cumulativePairing, hloss, heff, List.length_cons, Nat.cast_add, Nat.cast_one]
    linarith

theorem computedHistory_uniform_regret {a n : ℕ} (hn : 0 < n)
    (loss : List (Fin a) → Fin a → Fin n → ℚ) (eta theta : ℚ)
    (heta : 0 < eta ∧ eta ≤ 1 / 4) (ht : 0 < theta ∧ theta ≤ 1 / 2)
    (hl : ∀ h x i, 0 ≤ loss h x i ∧ loss h x i ≤ 1)
    (comparator : Fin n → ℝ) (hu : ∀ i, 0 ≤ comparator i) (hsu : ∑ i, comparator i = 1)
    (past : List (Fin a)) :
    (eta : ℝ) * cumulativePairing (fun h x i => (loss h x i : ℝ))
      (fun h => normalizedReal (rationalHistory (computedHistoryMultipliers loss eta theta) h)) comparator past ≤
        Real.log n + (eta : ℝ) ^ 2 / 2 * past.length *
          (1 + 2 * (theta : ℝ) / (eta : ℝ)) ^ 2 + 2 * (theta : ℝ) * past.length := by
  let multipliers := computedHistoryMultipliers loss eta theta
  let probability := fun h => normalizedReal (rationalHistory multipliers h)
  let effective := fun h x i => effectiveLoss (eta : ℝ) (multipliers h x i : ℝ)
  let error := 2 * (theta : ℝ) / (eta : ℝ)
  have hetaR : (0 : ℝ) < (eta : ℝ) := by exact_mod_cast heta.1
  have hx : ∀ h x i, 0 ≤ eta * loss h x i ∧ eta * loss h x i ≤ 1 / 4 := by
    intro h x i
    exact ⟨mul_nonneg heta.1.le (hl h x i).1,
      (mul_le_of_le_one_right heta.1.le (hl h x i).2).trans heta.2⟩
  have hm : ∀ h x i, 0 < multipliers h x i := fun h x i => (expMultiplierNative_unit _ _ (hx h x i) ht).1
  have hmUpper : ∀ h x i, multipliers h x i ≤ 1 := fun h x i => (expMultiplierNative_unit _ _ (hx h x i) ht).2
  have hc : ∀ h x i, effective h x i ≤ 1 + error := fun h x i =>
    (computedMultiplier_loss_unit eta (loss h x i) theta heta.1 (hl h x i) heta.2 ht).2
  have he := rationalHistory_effective_regret hn multipliers (eta : ℝ) (1 + error) hetaR hm hmUpper hc
    comparator hu hsu past
  have hcompare := cumulative_perturbation (fun h x i => (loss h x i : ℝ)) effective probability comparator error
    (fun h i => (normalizedReal_positive hn _ (rationalHistory_positive multipliers hm h) i).le)
    (fun h => normalizedReal_sum hn _ (rationalHistory_positive multipliers hm h)) hu hsu
    (fun h x i => computedMultiplier_effectiveLoss eta (loss h x i) theta heta.1 (hx h x i) ht) past
  have hmul := mul_le_mul_of_nonneg_left hcompare hetaR.le
  have hcancel : (eta : ℝ) * ((past.length : ℝ) * error) = 2 * (theta : ℝ) * past.length := by
    dsimp [error]
    field_simp
  rw [mul_add, hcancel] at hmul
  dsimp [multipliers, probability, effective, error] at he hmul
  linarith

theorem computedHistory_expected_regret {a n : ℕ} (hn : 0 < n)
    (transition : List (Fin a) → Fin a → ℝ)
    (hp : ∀ h x, 0 ≤ transition h x) (hs : ∀ h, ∑ x, transition h x = 1)
    (loss : List (Fin a) → Fin a → Fin n → ℚ) (eta theta : ℚ)
    (heta : 0 < eta ∧ eta ≤ 1 / 4) (ht : 0 < theta ∧ theta ≤ 1 / 2)
    (hl : ∀ h x i, 0 ≤ loss h x i ∧ loss h x i ≤ 1) (T : ℕ)
    (selectedComparator : List (Fin a) → Fin n → ℝ)
    (hSelected : ∀ h, selectedComparator h ∈ simplexComparators n) :
    (eta : ℝ) * historyMean transition T (fun past =>
      cumulativePairing (fun h _x i => conditionalDirection transition (fun h x i => (loss h x i : ℝ)) h i)
        (fun h => normalizedReal (rationalHistory (computedHistoryMultipliers loss eta theta) h))
        (selectedComparator past) past) ≤
          2 * Real.log n + (eta : ℝ) ^ 2 / 2 * T *
            ((1 + 2 * (theta : ℝ) / (eta : ℝ)) ^ 2 + 1) + 2 * (theta : ℝ) * T := by
  let empirical := fun h x i => (loss h x i : ℝ)
  let noise := fun h x i => empirical h x i - conditionalDirection transition empirical h i
  let actual := fun h => normalizedReal (rationalHistory (computedHistoryMultipliers loss eta theta) h)
  have hetaR : (0 : ℝ) < (eta : ℝ) := by exact_mod_cast heta.1
  have hlR : ∀ h x i, 0 ≤ empirical h x i ∧ empirical h x i ≤ 1 := by
    intro h x i
    change (0 : ℝ) ≤ (loss h x i : ℝ) ∧ (loss h x i : ℝ) ≤ 1
    exact ⟨by exact_mod_cast (hl h x i).1, by exact_mod_cast (hl h x i).2⟩
  let bound := Real.log n + (eta : ℝ) ^ 2 / 2 * T *
    (1 + 2 * (theta : ℝ) / (eta : ℝ)) ^ 2 + 2 * (theta : ℝ) * T
  have hActual : ∀ past, past.length = T → ∀ u, u ∈ simplexComparators n →
      (eta : ℝ) * cumulativePairing empirical actual u past ≤ bound := by
    intro past hlength u hu
    have he := computedHistory_uniform_regret hn loss eta theta heta ht hl u hu.1 hu.2 past
    simpa only [hlength, empirical, actual, bound] using he
  have he := expected_regret_with_constructed_auxiliary hn transition hp hs empirical noise
    (conditionalDirection_noise_mean_zero transition hs empirical)
    (conditionalDirection_noise_bound transition hp hs empirical hlR) actual (eta : ℝ) bound hetaR.le T
    hActual selectedComparator hSelected
  have htrue : (fun h x i => empirical h x i - noise h x i) =
      fun h _x i => conditionalDirection transition empirical h i := by
    funext h x i
    dsimp [noise]
    ring
  rw [htrue] at he
  dsimp [bound, empirical, actual] at he
  convert he using 1
  ring

end SparseMW
end Blotto
