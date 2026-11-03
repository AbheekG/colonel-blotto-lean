import Blotto.AdaptiveRoundedFieldHistory

/-! Uniform regret for any constructed positive rational multiplier history
with a proved bounded loss perturbation. This is used by stored-product rounding
whose ratio depends on the past weight; no fixed multiplier recurrence is assumed. -/

namespace Blotto
open scoped BigOperators Classical
namespace SparseMW

theorem rationalHistory_original_regret {a n : ℕ} (hn : 0 < n)
    (multipliers : List (Fin a) → Fin a → Fin n → ℚ)
    (loss : List (Fin a) → Fin a → Fin n → ℝ) (eta error : ℝ) (heta : 0 < eta)
    (hm : ∀ h x i, 0 < multipliers h x i) (hmUpper : ∀ h x i, multipliers h x i ≤ 1)
    (hLoss : ∀ h x i, 0 ≤ loss h x i ∧ loss h x i ≤ 1)
    (hPerturb : ∀ h x i, loss h x i ≤ effectiveLoss eta (multipliers h x i : ℝ) ∧
      effectiveLoss eta (multipliers h x i : ℝ) ≤ loss h x i + error)
    (u : Fin n → ℝ) (hu : ∀ i, 0 ≤ u i) (hsu : ∑ i, u i = 1) (past : List (Fin a)) :
    eta * cumulativePairing loss (fun h => normalizedReal (rationalHistory multipliers h)) u past ≤
      Real.log n + (eta ^ 2 / 2) * past.length * (1 + error) ^ 2 + eta * past.length * error := by
  let probability := fun h => normalizedReal (rationalHistory multipliers h)
  let effective := fun h x i => effectiveLoss eta (multipliers h x i : ℝ)
  have he := rationalHistory_effective_regret hn multipliers eta (1 + error) heta hm hmUpper
    (fun h x i => (hPerturb h x i).2.trans (by linarith [(hLoss h x i).2])) u hu hsu past
  have hc := cumulative_perturbation loss effective probability u error
    (fun h i => (normalizedReal_positive hn _ (rationalHistory_positive multipliers hm h) i).le)
    (fun h => normalizedReal_sum hn _ (rationalHistory_positive multipliers hm h)) hu hsu hPerturb past
  have hm := mul_le_mul_of_nonneg_left hc heta.le
  dsimp only [effective, probability] at hm
  nlinarith

theorem rationalHistory_expected_original_regret {a n : ℕ} (hn : 0 < n)
    (transition : List (Fin a) → Fin a → ℝ)
    (hp : ∀ h x, 0 ≤ transition h x) (hs : ∀ h, ∑ x, transition h x = 1)
    (multipliers : List (Fin a) → Fin a → Fin n → ℚ)
    (loss : List (Fin a) → Fin a → Fin n → ℝ) (eta error : ℝ) (heta : 0 < eta)
    (hm : ∀ h x i, 0 < multipliers h x i) (hmUpper : ∀ h x i, multipliers h x i ≤ 1)
    (hLoss : ∀ h x i, 0 ≤ loss h x i ∧ loss h x i ≤ 1)
    (hPerturb : ∀ h x i, loss h x i ≤ effectiveLoss eta (multipliers h x i : ℝ) ∧
      effectiveLoss eta (multipliers h x i : ℝ) ≤ loss h x i + error)
    (T : ℕ) (selectedComparator : List (Fin a) → Fin n → ℝ)
    (hSelected : ∀ h, selectedComparator h ∈ simplexComparators n) :
    eta * historyMean transition T (fun past =>
      cumulativePairing (fun h _x i => conditionalDirection transition loss h i)
        (fun h => normalizedReal (rationalHistory multipliers h)) (selectedComparator past) past) ≤
        2 * Real.log n + (eta ^ 2 / 2) * T * ((1 + error) ^ 2 + 1) + eta * T * error := by
  let noise := fun h x i => loss h x i - conditionalDirection transition loss h i
  let actual := fun h => normalizedReal (rationalHistory multipliers h)
  let bound := Real.log n + (eta ^ 2 / 2) * T * (1 + error) ^ 2 + eta * T * error
  have hpath : ∀ past, past.length = T → ∀ u, u ∈ simplexComparators n →
      eta * cumulativePairing loss actual u past ≤ bound := by
    intro past hlength u hu
    simpa only [hlength, actual, bound] using
      rationalHistory_original_regret hn multipliers loss eta error heta hm hmUpper hLoss hPerturb u hu.1 hu.2 past
  have he := expected_regret_with_constructed_auxiliary hn transition hp hs loss noise
    (conditionalDirection_noise_mean_zero transition hs loss)
    (conditionalDirection_noise_bound transition hp hs loss hLoss) actual eta bound heta.le T hpath selectedComparator hSelected
  have htrue : (fun h x i => loss h x i - noise h x i) = fun h _x i => conditionalDirection transition loss h i := by
    funext h x i
    dsimp [noise]
    ring
  rw [htrue] at he
  dsimp [actual, bound] at he
  convert he using 1
  ring

end SparseMW
end Blotto
