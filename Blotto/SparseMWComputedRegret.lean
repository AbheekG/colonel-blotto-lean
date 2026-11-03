import Blotto.SparseMWComputedMultiplier
import Blotto.SparseMWRationalUpdate

/-! Deterministic regret for an actual rational Taylor/rounded trajectory,
measured against the original nonnegative losses. This does not implement
implicit product-law storage or the learner's stochastic/security argument. -/

namespace Blotto
open scoped BigOperators Classical
namespace SparseMW

def computedMultipliers {n : ℕ} (loss : ℕ → Fin n → ℚ) (eta theta : ℚ) : ℕ → Fin n → ℚ :=
  fun t i => expMultiplierNative (eta * loss t i) theta

theorem computed_regret_comparison {n : ℕ} (probability comparator : Fin n → ℝ)
    (loss effective : Fin n → ℝ) (error : ℝ)
    (hp : ∀ i, 0 ≤ probability i) (_hs : ∑ i, probability i = 1)
    (hu : ∀ i, 0 ≤ comparator i) (hsu : ∑ i, comparator i = 1)
    (hl : ∀ i, loss i ≤ effective i ∧ effective i ≤ loss i + error) :
    (∑ i, (probability i - comparator i) * loss i) ≤
      (∑ i, (probability i - comparator i) * effective i) + error := by
  have hleft : (∑ i, probability i * loss i) ≤ ∑ i, probability i * effective i :=
    Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hl i).1 (hp i))
  have hright : (∑ i, comparator i * effective i) ≤ (∑ i, comparator i * loss i) + error := by
    calc
      _ ≤ ∑ i, comparator i * (loss i + error) :=
        Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hl i).2 (hu i))
      _ = _ := by simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hsu, one_mul]
  simp only [sub_mul, Finset.sum_sub_distrib]
  linarith

theorem computed_native_uniform_regret {n : ℕ} (hn : 0 < n) (comparator : Fin n → ℝ)
    (loss : ℕ → Fin n → ℚ) (eta theta : ℚ)
    (heta : 0 < eta ∧ eta ≤ 1 / 4) (ht : 0 < theta ∧ theta ≤ 1 / 2)
    (hu : ∀ i, 0 ≤ comparator i) (hsu : ∑ i, comparator i = 1)
    (hl : ∀ t i, 0 ≤ loss t i ∧ loss t i ≤ 1) (T : ℕ) :
    (eta : ℝ) * (∑ t ∈ Finset.range T, ∑ i,
      (normalizedReal (multiplierTrajectory (computedMultipliers loss eta theta) t) i - comparator i) *
        (loss t i : ℝ)) ≤
      Real.log n + (eta : ℝ) ^ 2 / 2 * (T : ℝ) *
        (1 + 2 * (theta : ℝ) / (eta : ℝ)) ^ 2 + 2 * (theta : ℝ) * T := by
  let multipliers := computedMultipliers loss eta theta
  let probability := fun t => normalizedReal (multiplierTrajectory multipliers t)
  let effective := fun t i => effectiveLoss (eta : ℝ) (multipliers t i : ℝ)
  let error := 2 * (theta : ℝ) / (eta : ℝ)
  have hetaR : (0 : ℝ) < (eta : ℝ) := by exact_mod_cast heta.1
  have hx : ∀ t i, 0 ≤ eta * loss t i ∧ eta * loss t i ≤ 1 / 4 := by
    intro t i
    exact ⟨mul_nonneg heta.1.le (hl t i).1,
      (mul_le_of_le_one_right heta.1.le (hl t i).2).trans heta.2⟩
  have hm : ∀ t i, 0 < multipliers t i := fun t i => (expMultiplierNative_unit _ _ (hx t i) ht).1
  have hp : ∀ t i, 0 < probability t i := fun t i =>
    normalizedReal_positive hn _ (multiplierTrajectory_positive multipliers hm t) i
  have hs : ∀ t, ∑ i, probability t i = 1 := fun t =>
    normalizedReal_sum hn _ (multiplierTrajectory_positive multipliers hm t)
  have hb : ∀ t i, 0 ≤ effective t i ∧ effective t i ≤ 1 + error := by
    intro t i
    exact computedMultiplier_loss_unit eta (loss t i) theta heta.1 (hl t i) heta.2 ht
  have htR : (0 : ℝ) < (theta : ℝ) := by exact_mod_cast ht.1
  have hcap : 0 ≤ 1 + error := by dsimp [error]; positivity
  have hsharp := finite_uniform_bounded_sharp_regret hn comparator probability effective (eta : ℝ) (1 + error)
    hu hsu hp hs (normalizedTrajectory_uniform multipliers) hetaR.le hcap hb
    (fun t => normalizedReal_update hn _ _ (multiplierTrajectory_positive multipliers hm t) (hm t)
      (eta : ℝ) (ne_of_gt hetaR)) T
  have hcompare : (∑ t ∈ Finset.range T, ∑ i, (probability t i - comparator i) * (loss t i : ℝ)) ≤
      (∑ t ∈ Finset.range T, ∑ i, (probability t i - comparator i) * effective t i) + T * error := by
    calc
      _ ≤ ∑ t ∈ Finset.range T, ((∑ i, (probability t i - comparator i) * effective t i) + error) := by
        apply Finset.sum_le_sum
        intro t _
        exact computed_regret_comparison (probability t) comparator (fun i => (loss t i : ℝ)) (effective t)
          error (fun i => (hp t i).le) (hs t) hu hsu
          (fun i => computedMultiplier_effectiveLoss eta (loss t i) theta heta.1 (hx t i) ht)
      _ = _ := by
        rw [Finset.sum_add_distrib]
        simp
  have hmul := mul_le_mul_of_nonneg_left hcompare hetaR.le
  have hcancel : (eta : ℝ) * ((T : ℝ) * error) = 2 * (theta : ℝ) * T := by
    dsimp [error]
    field_simp
  dsimp [probability, multipliers, error] at hmul hsharp
  rw [mul_add, hcancel] at hmul
  linarith

end SparseMW
end Blotto
