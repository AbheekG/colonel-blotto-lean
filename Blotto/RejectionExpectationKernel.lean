import Blotto.RationalProposalKernelEvents
import Blotto.FiniteRejectionAttempts

/-! A first-success loop in probability-kernel semantics is the actual short-
circuit decision rule. Uniform one-attempt errors add through a finite cap;
failure probabilities are derived rather than assumed independent events. -/

namespace Blotto
open scoped Classical
namespace BoundedExpectationKernel

noncomputable def firstSuccess {α : Type*} (attempt : BoundedExpectationKernel (Option α)) :
    ℕ → BoundedExpectationKernel (Option α)
  | 0 => point none
  | n + 1 => attempt.bind (fun result =>
      match result with
      | none => attempt.firstSuccess n
      | some x => point (some x))

theorem firstSuccess_close {α : Type*} (a b : BoundedExpectationKernel (Option α))
    (error : ℝ) (hn : 0 ≤ error) (h : a.Close b error) (n : ℕ) :
    (a.firstSuccess n).Close (b.firstSuccess n) ((n : ℝ) * error) := by
  induction n with
  | zero => intro f _hf; simp only [firstSuccess, sub_self, abs_zero, Nat.cast_zero, zero_mul, le_refl]
  | succ n ih =>
    have hc : ∀ result : Option α,
        (match result with | none => a.firstSuccess n | some x => point (some x)).Close
        (match result with | none => b.firstSuccess n | some x => point (some x)) ((n : ℝ) * error) := by
      intro result
      cases result with
      | none => exact ih
      | some x => intro f _hf; simp only [sub_self, abs_zero]; positivity
    have he := bind_close a b _ _ error ((n : ℝ) * error) h hc
    intro f hf
    have ht := he f hf
    simpa only [firstSuccess, Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_comm] using ht

theorem firstSuccess_mean_recurrence {α : Type*} (a : BoundedExpectationKernel (Option α))
    (n : ℕ) (f : Option α → ℝ) :
    (a.firstSuccess (n + 1)).mean f = a.mean (fun result =>
      match result with | none => (a.firstSuccess n).mean f | some x => f (some x)) := by
  change a.mean (fun result => (match result with
    | none => a.firstSuccess n | some x => point (some x)).mean f) = _
  apply congrArg a.mean
  funext result
  cases result <;> rfl

end BoundedExpectationKernel
end Blotto
