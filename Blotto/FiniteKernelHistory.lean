import Blotto.AdaptiveKernelHistory
import Blotto.FiniteAdaptiveExpectation

/-! Forward kernel execution equals the earlier exact finite-history mean.
This join lets sampler comparison transfer proved finite-training bad events;
no finite-history enumeration is part of native sampling. -/

namespace Blotto
open scoped BigOperators Classical

noncomputable def finiteTransitionKernel {a : ℕ} (transition : List (Fin a) → Fin a → ℝ)
    (hp : ∀ h x, 0 ≤ transition h x) (hs : ∀ h, ∑ x, transition h x = 1)
    (h : List (Fin a)) : BoundedExpectationKernel (Fin a) where
  mean := fun f => ∑ x, transition h x * f x
  constant := by intro c; rw [← Finset.sum_mul, hs, one_mul]
  monotone := by intro f g he; exact Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (he x) (hp h x))
  add := by intro f g; simp only [mul_add, Finset.sum_add_distrib]

theorem historyEvolution_finite_mean {a : ℕ} (transition : List (Fin a) → Fin a → ℝ)
    (hp : ∀ h x, 0 ≤ transition h x) (hs : ∀ h, ∑ x, transition h x = 1)
    (T : ℕ) (test : List (Fin a) → ℝ) :
    (BoundedExpectationKernel.historyEvolution (finiteTransitionKernel transition hp hs) T).mean test =
      SparseMW.historyMean transition T test := by
  induction T generalizing test with
  | zero => simp [BoundedExpectationKernel.historyEvolution, BoundedExpectationKernel.point, SparseMW.historyMean_zero]
  | succ T ih =>
    change (BoundedExpectationKernel.historyEvolution (finiteTransitionKernel transition hp hs) T).mean
      (fun h => ∑ x, transition h x * test (x :: h)) = _
    rw [ih, SparseMW.historyMean_succ]

theorem finiteHistory_event_transfer {a : ℕ} (actual : List (Fin a) → BoundedExpectationKernel (Fin a))
    (transition : List (Fin a) → Fin a → ℝ)
    (hp : ∀ h x, 0 ≤ transition h x) (hs : ∀ h, ∑ x, transition h x = 1)
    (error : ℝ) (herror : 0 ≤ error)
    (hstep : ∀ h, (actual h).Close (finiteTransitionKernel transition hp hs h) error)
    (T : ℕ) (event : Set (List (Fin a))) :
    |(BoundedExpectationKernel.historyEvolution actual T).mean (fun h => if h ∈ event then 1 else 0) -
      SparseMW.historyMean transition T (fun h => if h ∈ event then 1 else 0)| ≤ (T : ℝ) * error := by
  have he := BoundedExpectationKernel.historyEvolution_close actual (finiteTransitionKernel transition hp hs)
    error herror hstep T (fun h => if h ∈ event then 1 else 0) (fun h => by split_ifs <;> norm_num)
  rw [historyEvolution_finite_mean] at he
  exact he

end Blotto
