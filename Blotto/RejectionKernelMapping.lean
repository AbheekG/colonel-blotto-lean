import Blotto.RejectionKernelTargetLaw

/-! Mapping the whole accepted record commutes with first-success execution.
Failure remains none. This connects augmented proposal laws to their true
labelled outputs without selecting independent coordinates. -/

namespace Blotto
open scoped Classical
namespace BoundedExpectationKernel

theorem firstSuccess_map_mean {α β : Type*} (attempt : BoundedExpectationKernel (Option α))
    (output : α → β) (n : ℕ) (f : Option β → ℝ) :
    (attempt.firstSuccess n).mean (fun result => f (result.map output)) =
      ((attempt.map (fun result => result.map output)).firstSuccess n).mean f := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [firstSuccess_mean_recurrence, firstSuccess_mean_recurrence]
    change attempt.mean (fun result => match result with
      | none => (attempt.firstSuccess n).mean (fun result => f (result.map output))
      | some x => f ((some x).map output)) =
      attempt.mean (fun result => match result.map output with
      | none => ((attempt.map (fun result => result.map output)).firstSuccess n).mean f
      | some x => f (some x))
    rw [ih]
    apply congrArg attempt.mean
    funext result
    cases result <;> rfl

end BoundedExpectationKernel
end Blotto
