import Blotto.RejectionExpectationKernel

/-! A one-attempt reject/target mixture yields the exact truncated geometric
first-success law. The target mean need not be a finite support enumeration;
the certificate is the one-attempt identity proved for the proposal. -/

namespace Blotto
namespace BoundedExpectationKernel

theorem firstSuccess_target_mean {α : Type*} (attempt : BoundedExpectationKernel (Option α))
    (target : BoundedExpectationKernel α) (acceptance : ℝ)
    (hAttempt : ∀ f : Option α → ℝ, attempt.mean f =
      acceptance * target.mean (fun x => f (some x)) + (1 - acceptance) * f none)
    (n : ℕ) (f : Option α → ℝ) :
    (attempt.firstSuccess n).mean f =
      (1 - rejectionFailure acceptance n) * target.mean (fun x => f (some x)) +
        rejectionFailure acceptance n * f none := by
  induction n with
  | zero => simp [firstSuccess, point, rejectionFailure]
  | succ n ih =>
    rw [firstSuccess_mean_recurrence, hAttempt]
    have hSome : target.mean (fun x => match some x with
        | none => (attempt.firstSuccess n).mean f | some x => f (some x)) = target.mean (fun x => f (some x)) := rfl
    rw [hSome]
    simp only at *
    rw [ih]
    unfold rejectionFailure
    rw [pow_succ]
    ring

theorem firstSuccess_fallback_mean {α : Type*} (attempt : BoundedExpectationKernel (Option α))
    (target : BoundedExpectationKernel α) (acceptance : ℝ)
    (hAttempt : ∀ f : Option α → ℝ, attempt.mean f =
      acceptance * target.mean (fun x => f (some x)) + (1 - acceptance) * f none)
    (n : ℕ) (fallback : α) (f : α → ℝ) :
    ((attempt.firstSuccess n).map (fun result => result.getD fallback)).mean f =
      (1 - rejectionFailure acceptance n) * target.mean f + rejectionFailure acceptance n * f fallback := by
  exact firstSuccess_target_mean attempt target acceptance hAttempt n (fun result => f (result.getD fallback))

theorem firstSuccess_fallback_error {α : Type*} (attempt : BoundedExpectationKernel (Option α))
    (target : BoundedExpectationKernel α) (acceptance : ℝ) (hp : 0 ≤ acceptance) (h1 : acceptance ≤ 1)
    (hAttempt : ∀ f : Option α → ℝ, attempt.mean f =
      acceptance * target.mean (fun x => f (some x)) + (1 - acceptance) * f none)
    (n : ℕ) (fallback : α) :
    ((attempt.firstSuccess n).map (fun result => result.getD fallback)).Close target (rejectionFailure acceptance n) := by
  intro f hf
  rw [firstSuccess_fallback_mean attempt target acceptance hAttempt n fallback f]
  have hTarget := target.mean_unit f hf
  exact rejectionFallback_event_error (rejectionFailure_unit hp h1 n).1 hTarget.1 hTarget.2 (hf fallback).1 (hf fallback).2

end BoundedExpectationKernel
end Blotto
