import Blotto.NativePreparedTrainingHistory
import Blotto.AdaptiveSamplingPrecision

/-! The actual fixed-block adaptive prepared sampler selects positive rational
per-call accuracy and native field precision for a requested total error.
A horizon-local uniform bit cap remains an explicit resource certificate. -/

namespace Blotto
open scoped Classical
namespace NativePreparedTrainingHistory

theorem scheduled_run_bounded_error {m : ℕ}
    (a b : List (Observation m) → PreparedProductSampler m) (values : RationalFieldSelector m)
    (accuracy : ℚ) (ha : 0 < accuracy) (T B : ℕ)
    (hWidth : ∀ history, history.length < T →
      PreparedProductTransition.bitBudget (a history) (b history) values
        (adaptiveDrawTolerance accuracy T) (adaptiveDrawTolerance accuracy T) (adaptiveFieldPrecision accuracy T) ≤ B)
    (test : List (Observation m) → ℝ) (htest : ∀ history, 0 ≤ test history ∧ test history ≤ 1) :
    |(fairBitKernel (T * B)).mean (fun bits => test
      (run a b values (adaptiveDrawTolerance accuracy T) (adaptiveDrawTolerance accuracy T)
        (adaptiveFieldPrecision accuracy T) B T bits [])) -
      (BoundedExpectationKernel.historyRun (idealStep a b values) T []).mean test| ≤ (accuracy : ℝ) := by
  have h := run_bounded_error_before a b values
    (adaptiveDrawTolerance accuracy T) (adaptiveDrawTolerance accuracy T)
    (adaptiveDrawTolerance_positive accuracy ha T) (adaptiveDrawTolerance_positive accuracy ha T)
    (adaptiveFieldPrecision accuracy T) B T hWidth T [] (by simp) test htest
  exact h.trans (by simpa only [two_mul] using adaptiveTotalDrawError accuracy ha T)

theorem scheduled_run_event_error {m : ℕ}
    (a b : List (Observation m) → PreparedProductSampler m) (values : RationalFieldSelector m)
    (accuracy : ℚ) (ha : 0 < accuracy) (T B : ℕ)
    (hWidth : ∀ history, history.length < T →
      PreparedProductTransition.bitBudget (a history) (b history) values
        (adaptiveDrawTolerance accuracy T) (adaptiveDrawTolerance accuracy T) (adaptiveFieldPrecision accuracy T) ≤ B)
    (event : Set (List (Observation m))) :
    |(fairBitKernel (T * B)).mean (fun bits => if
      run a b values (adaptiveDrawTolerance accuracy T) (adaptiveDrawTolerance accuracy T)
        (adaptiveFieldPrecision accuracy T) B T bits [] ∈ event then 1 else 0) -
      (BoundedExpectationKernel.historyRun (idealStep a b values) T []).mean
        (fun h => if h ∈ event then 1 else 0)| ≤ (accuracy : ℝ) :=
  scheduled_run_bounded_error a b values accuracy ha T B hWidth (fun h => if h ∈ event then 1 else 0)
    (fun h => by split_ifs <;> norm_num)

end NativePreparedTrainingHistory
end Blotto
