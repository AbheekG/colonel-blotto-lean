import Blotto.BoundedExpectationKernel
import Blotto.PositiveRationalChoiceLaw

/-! Actual finite-block and normalized ideal rational choices instantiate the
kernel interface. Adaptive bind bounds can therefore use actual bounded test
errors rather than supplied statistical assumptions. -/

namespace Blotto
open MeasureTheory
open scoped BigOperators Classical

noncomputable def fairBitKernel (N : ℕ) : BoundedExpectationKernel (Fin N → Bool) where
  mean := fun f => ∫ bits, f bits ∂(fairBitLaw N : Measure (Fin N → Bool))
  constant := by intro c; simp
  monotone := by
    intro f g h
    exact integral_mono Integrable.of_finite Integrable.of_finite h
  add := by intro f g; exact integral_add Integrable.of_finite Integrable.of_finite

namespace BoundedExpectationKernel

noncomputable def point {α : Type*} (value : α) : BoundedExpectationKernel α where
  mean := fun f => f value
  constant := fun _ => rfl
  monotone := fun _f _g h => h value
  add := fun _ _ => rfl

noncomputable def map {α β : Type*} (k : BoundedExpectationKernel α) (f : α → β) : BoundedExpectationKernel β :=
  k.bind (fun x => point (f x))

theorem map_close {α β : Type*} (a b : BoundedExpectationKernel α) (f : α → β) (error : ℝ)
    (h : a.Close b error) : (a.map f).Close (b.map f) error := by
  intro g hg
  exact h (fun x => g (f x)) (fun x => hg _)

end BoundedExpectationKernel

noncomputable def normalizedRationalKernel {r : ℕ} (weights : Fin r → ℚ)
    (hn : ∀ i, 0 ≤ weights i) (ht : 0 < ∑ i, weights i) : BoundedExpectationKernel (Option (Fin r)) where
  mean := fun f => ∑ i, ((weights i / ∑ j, weights j : ℚ) : ℝ) * f (some i)
  constant := by
    intro c
    rw [← Finset.sum_mul]
    have hs : (∑ i, ((weights i / ∑ j, weights j : ℚ) : ℝ)) = 1 := by
      have he : (∑ i, weights i / ∑ j, weights j) = (1 : ℚ) := by
        simp only [div_eq_mul_inv]
        rw [← Finset.sum_mul, mul_inv_cancel₀ (ne_of_gt ht)]
      exact_mod_cast he
    rw [hs, one_mul]
  monotone := by
    intro f g h
    apply Finset.sum_le_sum
    intro i _
    apply mul_le_mul_of_nonneg_left (h _)
    exact_mod_cast (div_nonneg (hn i) ht.le)
  add := by intro f g; simp only [mul_add, Finset.sum_add_distrib]

noncomputable def positiveChoiceKernel {r : ℕ} (weights : Fin r → ℚ)
    (hn : ∀ i, 0 ≤ weights i) (K : ℕ) : BoundedExpectationKernel (Option (Fin r)) :=
  (fairBitKernel (3 * (r - 1 + K))).map
    (fun bits => positiveRationalChoice weights hn K (finiteBitReader bits))

theorem positiveChoiceKernel_close {r : ℕ} (weights : Fin r → ℚ) (hn : ∀ i, 0 ≤ weights i)
    (hr : 0 < r) (ht : 0 < ∑ i, weights i) (K : ℕ) :
    (positiveChoiceKernel weights hn K).Close (normalizedRationalKernel weights hn ht) (1 / (2 : ℝ) ^ K) := by
  intro f hf
  exact positiveRationalChoice_mean_error weights hn hr ht K f hf

end Blotto
