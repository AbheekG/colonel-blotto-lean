import Blotto.FiniteAdaptiveExpectation

/-! Uniform comparator inequalities are combined pathwise before expectation.
Predictable auxiliary-minus-actual noise cancels; a maximizing comparator is
never used in a mean-zero claim. Actual prox/learner and saddle-game bindings
must supply the explicitly stated pathwise contracts. -/

namespace Blotto
open scoped BigOperators Classical
namespace SparseMW

noncomputable def cumulativePairing {a n : ℕ} (direction : List (Fin a) → Fin a → Fin n → ℝ)
    (actual : List (Fin a) → Fin n → ℝ) (comparator : Fin n → ℝ) : List (Fin a) → ℝ
  | [] => 0
  | x :: past => cumulativePairing direction actual comparator past +
      ∑ i, direction past x i * (actual past i - comparator i)

theorem cumulative_true_empirical_identity {a n : ℕ}
    (empirical noise : List (Fin a) → Fin a → Fin n → ℝ)
    (actual auxiliary : List (Fin a) → Fin n → ℝ) (comparator : Fin n → ℝ)
    (past : List (Fin a)) :
    cumulativePairing (fun h x i => empirical h x i - noise h x i) actual comparator past =
      cumulativePairing empirical actual comparator past +
      cumulativePairing (fun h x i => -noise h x i) auxiliary comparator past +
      accumulatedNoise noise (fun h i => auxiliary h i - actual h i) past := by
  induction past with
  | nil => simp [cumulativePairing, accumulatedNoise]
  | cons x past ih =>
    rw [cumulativePairing, cumulativePairing, cumulativePairing, accumulatedNoise, ih]
    have he : (∑ i, (empirical past x i - noise past x i) * (actual past i - comparator i)) =
        (∑ i, empirical past x i * (actual past i - comparator i)) +
        (∑ i, -noise past x i * (auxiliary past i - comparator i)) +
        ∑ i, noise past x i * (auxiliary past i - actual past i) := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [he]
    ring

theorem uniform_true_regret_pathwise {a n : ℕ}
    (empirical noise : List (Fin a) → Fin a → Fin n → ℝ)
    (actual auxiliary : List (Fin a) → Fin n → ℝ) (comparators : Set (Fin n → ℝ))
    (boundActual boundAuxiliary : ℝ) (past : List (Fin a))
    (hActual : ∀ u ∈ comparators, cumulativePairing empirical actual u past ≤ boundActual)
    (hAuxiliary : ∀ u ∈ comparators,
      cumulativePairing (fun h x i => -noise h x i) auxiliary u past ≤ boundAuxiliary) :
    ∀ u ∈ comparators,
      cumulativePairing (fun h x i => empirical h x i - noise h x i) actual u past ≤
        boundActual + boundAuxiliary +
          accumulatedNoise noise (fun h i => auxiliary h i - actual h i) past := by
  intro u hu
  rw [cumulative_true_empirical_identity]
  linarith [hActual u hu, hAuxiliary u hu]

theorem expected_uniform_true_regret {a n : ℕ}
    (transition : List (Fin a) → Fin a → ℝ)
    (hp : ∀ past x, 0 ≤ transition past x) (hs : ∀ past, ∑ x, transition past x = 1)
    (empirical noise : List (Fin a) → Fin a → Fin n → ℝ)
    (hz : ∀ past i, ∑ x, transition past x * noise past x i = 0)
    (actual auxiliary : List (Fin a) → Fin n → ℝ) (comparators : Set (Fin n → ℝ))
    (boundActual boundAuxiliary : ℝ) (T : ℕ)
    (hActual : ∀ past, past.length = T → ∀ u, u ∈ comparators → cumulativePairing empirical actual u past ≤ boundActual)
    (hAuxiliary : ∀ past, past.length = T → ∀ u, u ∈ comparators →
      cumulativePairing (fun h x i => -noise h x i) auxiliary u past ≤ boundAuxiliary)
    (selectedComparator : List (Fin a) → Fin n → ℝ) (hSelected : ∀ past, selectedComparator past ∈ comparators) :
    historyMean transition T (fun past =>
      cumulativePairing (fun h x i => empirical h x i - noise h x i) actual (selectedComparator past) past) ≤
        boundActual + boundAuxiliary := by
  have hpath := fun past hlength => uniform_true_regret_pathwise empirical noise actual auxiliary comparators
    boundActual boundAuxiliary past (hActual past hlength) (hAuxiliary past hlength) (selectedComparator past) (hSelected past)
  have he := historyMean_monotone_at_length transition hp T _ _ hpath
  rw [historyMean_add, historyMean_constant transition hs,
    accumulated_auxiliary_actual_cancellation transition hs noise hz, add_zero] at he
  exact he

theorem expected_sampled_direction_regret {a n : ℕ}
    (transition : List (Fin a) → Fin a → ℝ)
    (hp : ∀ past x, 0 ≤ transition past x) (hs : ∀ past, ∑ x, transition past x = 1)
    (empirical : List (Fin a) → Fin a → Fin n → ℝ)
    (actual auxiliary : List (Fin a) → Fin n → ℝ) (comparators : Set (Fin n → ℝ))
    (boundActual boundAuxiliary : ℝ) (T : ℕ)
    (hActual : ∀ past, past.length = T → ∀ u, u ∈ comparators →
      cumulativePairing empirical actual u past ≤ boundActual)
    (hAuxiliary : ∀ past, past.length = T → ∀ u, u ∈ comparators →
      cumulativePairing (fun h x i => conditionalDirection transition empirical h i - empirical h x i)
        auxiliary u past ≤ boundAuxiliary)
    (selectedComparator : List (Fin a) → Fin n → ℝ) (hSelected : ∀ past, selectedComparator past ∈ comparators) :
    historyMean transition T (fun past =>
      cumulativePairing (fun h _x i => conditionalDirection transition empirical h i)
        actual (selectedComparator past) past) ≤ boundActual + boundAuxiliary := by
  let noise := fun h x i => empirical h x i - conditionalDirection transition empirical h i
  have hz := conditionalDirection_noise_mean_zero transition hs empirical
  have haux : ∀ past, past.length = T → ∀ u, u ∈ comparators →
      cumulativePairing (fun h x i => -noise h x i) auxiliary u past ≤ boundAuxiliary := by
    simpa only [noise, neg_sub] using hAuxiliary
  have he := expected_uniform_true_regret transition hp hs empirical noise hz actual auxiliary
    comparators boundActual boundAuxiliary T hActual haux selectedComparator hSelected
  have htrue : (fun h x i => empirical h x i - noise h x i) =
      fun h _x i => conditionalDirection transition empirical h i := by
    funext h x i
    dsimp [noise]
    ring
  rw [htrue] at he
  exact he

theorem expected_uniform_true_regret_scaled {a n : ℕ}
    (transition : List (Fin a) → Fin a → ℝ)
    (hp : ∀ past x, 0 ≤ transition past x) (hs : ∀ past, ∑ x, transition past x = 1)
    (empirical noise : List (Fin a) → Fin a → Fin n → ℝ)
    (hz : ∀ past i, ∑ x, transition past x * noise past x i = 0)
    (actual auxiliary : List (Fin a) → Fin n → ℝ) (comparators : Set (Fin n → ℝ))
    (eta boundActual boundAuxiliary : ℝ) (T : ℕ)
    (hActual : ∀ past, past.length = T → ∀ u, u ∈ comparators →
      eta * cumulativePairing empirical actual u past ≤ boundActual)
    (hAuxiliary : ∀ past, past.length = T → ∀ u, u ∈ comparators →
      eta * cumulativePairing (fun h x i => -noise h x i) auxiliary u past ≤ boundAuxiliary)
    (selectedComparator : List (Fin a) → Fin n → ℝ) (hSelected : ∀ past, selectedComparator past ∈ comparators) :
    eta * historyMean transition T (fun past =>
      cumulativePairing (fun h x i => empirical h x i - noise h x i) actual (selectedComparator past) past) ≤
        boundActual + boundAuxiliary := by
  have hpath : ∀ past, past.length = T →
      eta * cumulativePairing (fun h x i => empirical h x i - noise h x i) actual (selectedComparator past) past ≤
        boundActual + boundAuxiliary +
          eta * accumulatedNoise noise (fun h i => auxiliary h i - actual h i) past := by
    intro past hlength
    rw [cumulative_true_empirical_identity, mul_add, mul_add]
    linarith [hActual past hlength (selectedComparator past) (hSelected past),
      hAuxiliary past hlength (selectedComparator past) (hSelected past)]
  have he := historyMean_monotone_at_length transition hp T _ _ hpath
  rw [historyMean_mul, historyMean_add, historyMean_constant transition hs,
    historyMean_mul, accumulated_auxiliary_actual_cancellation transition hs noise hz, mul_zero, add_zero] at he
  exact he

end SparseMW
end Blotto
