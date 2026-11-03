import Blotto.RationalProposalNodeSampler
import Blotto.RationalFiniteAttemptMean

/-! The actual local positive-choice runtime has the exact normalized ideal
mean and a uniform bounded-bit mean error. The zero-weight filter is exact in
the ideal law; no minimum positive atom mass is assumed. -/

namespace Blotto
open MeasureTheory
open scoped BigOperators Classical

def finiteBitReader {N : ℕ} (bits : Fin N → Bool) (pos : ℕ) : Bool :=
  if h : pos < N then bits ⟨pos, h⟩ else false

def positiveChoiceAttempt {r : ℕ} (weights : Fin r → ℚ) (hn : ∀ i, 0 ≤ weights i)
    (hr : 0 < r) (ht : 0 < ∑ i, weights i) : RationalFiniteAttempt r r where
  weight := fun i => weights i / ∑ j, weights j
  nonnegative := fun i => div_nonneg (hn i) ht.le
  sum_one := by
    simp only [div_eq_mul_inv]
    rw [← Finset.sum_mul]
    exact mul_inv_cancel₀ (ne_of_gt ht)
  decode := fun i => if 0 < weights i then some i else none
  fallbackLabel := ⟨0, hr⟩

theorem positiveRationalChoice_eq_sample {r : ℕ} (weights : Fin r → ℚ) (hn : ∀ i, 0 ≤ weights i)
    (hr : 0 < r) (ht : 0 < ∑ i, weights i) (K : ℕ) (bits : ℕ → Bool) :
    positiveRationalChoice weights hn K bits =
      (positiveChoiceAttempt weights hn hr ht).sample K (fun j => bits j.val) := by
  unfold positiveRationalChoice
  rw [dite_eq_left hr]
  dsimp only
  rw [dite_eq_left ht]
  rfl

theorem positiveChoiceAttempt_idealMean {r : ℕ} (weights : Fin r → ℚ) (hn : ∀ i, 0 ≤ weights i)
    (hr : 0 < r) (ht : 0 < ∑ i, weights i) (f : Option (Fin r) → ℝ) :
    (positiveChoiceAttempt weights hn hr ht).idealMean f =
      ∑ i, ((weights i / ∑ j, weights j : ℚ) : ℝ) * f (some i) := by
  unfold RationalFiniteAttempt.idealMean positiveChoiceAttempt
  apply Finset.sum_congr rfl
  intro i _
  by_cases hp : 0 < weights i
  · simp only [hp, ite_true]
  · have hz : weights i = 0 := le_antisymm (le_of_not_gt hp) (hn i)
    simp [hz]

theorem positiveRationalChoice_mean_error {r : ℕ} (weights : Fin r → ℚ) (hn : ∀ i, 0 ≤ weights i)
    (hr : 0 < r) (ht : 0 < ∑ i, weights i) (K : ℕ) (f : Option (Fin r) → ℝ)
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) :
    |(∫ bits : Fin (3 * (r - 1 + K)) → Bool,
        f (positiveRationalChoice weights hn K (fun pos => finiteBitReader bits pos)) ∂(fairBitLaw (3 * (r - 1 + K)) : Measure (Fin (3 * (r - 1 + K)) → Bool))) -
      ∑ i, ((weights i / ∑ j, weights j : ℚ) : ℝ) * f (some i)| ≤ 1 / (2 : ℝ) ^ K := by
  let a := positiveChoiceAttempt weights hn hr ht
  have he := a.sampleMean_error K f hf
  rw [positiveChoiceAttempt_idealMean] at he
  have hSample : ∀ bits : Fin (3 * (r - 1 + K)) → Bool,
      positiveRationalChoice weights hn K (fun pos => finiteBitReader bits pos) = a.sample K bits := by
    intro bits
    rw [positiveRationalChoice_eq_sample weights hn hr ht]
    congr 1
    funext j
    have hj : j.val < 3 * (r - 1 + K) := j.isLt
    unfold finiteBitReader
    rw [dite_eq_left hj]
    congr 1
  simp_rw [hSample]
  exact he

end Blotto
