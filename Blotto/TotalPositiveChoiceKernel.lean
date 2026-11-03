import Blotto.RationalFiniteKernel

/-! Zero-mass and empty local choices are explicit deterministic failure in
both actual and ideal kernels. Positive totals retain the uniform mean error. -/

namespace Blotto
open scoped BigOperators Classical

noncomputable def totalNormalizedKernel {r : ℕ} (weights : Fin r → ℚ) (hn : ∀ i, 0 ≤ weights i) :
    BoundedExpectationKernel (Option (Fin r)) :=
  if ht : 0 < ∑ i, weights i then normalizedRationalKernel weights hn ht else BoundedExpectationKernel.point none

theorem positive_total_count {r : ℕ} (weights : Fin r → ℚ) (ht : 0 < ∑ i, weights i) : 0 < r := by
  by_contra hr
  have hz : r = 0 := by omega
  subst r
  simp at ht

theorem positiveChoiceKernel_zero {r : ℕ} (weights : Fin r → ℚ) (hn : ∀ i, 0 ≤ weights i)
    (ht : ¬ 0 < ∑ i, weights i) (K : ℕ) :
    positiveChoiceKernel weights hn K = BoundedExpectationKernel.point none := by
  have hSample : ∀ bits : ℕ → Bool, positiveRationalChoice weights hn K bits = none := by
    intro bits
    unfold positiveRationalChoice
    split
    · dsimp only
      rw [dite_eq_right ht]
    · rfl
  have hm : (positiveChoiceKernel weights hn K).mean = (BoundedExpectationKernel.point none).mean := by
    funext f
    change (fairBitKernel _).mean (fun bits => f (positiveRationalChoice weights hn K (finiteBitReader bits))) = f none
    simp_rw [hSample]
    exact (fairBitKernel _).constant _
  have hExt : ∀ a b : BoundedExpectationKernel (Option (Fin r)), a.mean = b.mean → a = b := by
    intro a b hab
    cases a
    cases b
    cases hab
    rfl
  exact hExt _ _ hm

theorem positiveChoiceKernel_total_close {r : ℕ} (weights : Fin r → ℚ) (hn : ∀ i, 0 ≤ weights i) (K : ℕ) :
    (positiveChoiceKernel weights hn K).Close (totalNormalizedKernel weights hn) (1 / (2 : ℝ) ^ K) := by
  unfold totalNormalizedKernel
  split
  · rename_i ht
    exact positiveChoiceKernel_close weights hn (positive_total_count weights ht) ht K
  · rename_i ht
    rw [positiveChoiceKernel_zero weights hn ht K]
    intro f _hf
    simp only [sub_self, abs_zero]
    positivity

end Blotto
