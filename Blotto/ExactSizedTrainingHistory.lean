import Blotto.ExactSizedTrainingTransition
import Blotto.NativeImplicitTrainingHistory

/-! Exact native draw replacements execute in the fixed-block adaptive trainer.
Equality holds on every seed, including the original overflow fallback. Source
seed-cap and convergence theorems can therefore be reused without a new oracle. -/

namespace Blotto.ExactSizedTrainingHistory
open ImplicitLeafCounts

abbrev Observation (m : ℕ) := ImplicitTrainingTransition.Observation m

def sample {m : ℕ} (first second : List (Observation m) → ExactSizedDraw m) (values : RationalFieldSelector m)
    (epsilonFirst epsilonSecond : ℚ) (K B : ℕ) (history : List (Observation m)) (bits : Fin B → Bool) : Observation m :=
  if hWidth : ExactSizedTrainingTransition.bitBudget (first history) (second history) values epsilonFirst epsilonSecond K ≤ B then
    ExactSizedTrainingTransition.sample (first history) (second history) values epsilonFirst epsilonSecond K
      (fun j => bits ⟨j.val, Nat.lt_of_lt_of_le j.isLt hWidth⟩)
  else (NativeImplicitTrainingHistory.fallbackRow (first history).model,
    NativeImplicitTrainingHistory.fallbackRow (second history).model, values.attempt.fallbackLabel)

theorem sample_refines {m : ℕ} (first second : List (Observation m) → ExactSizedDraw m) (values : RationalFieldSelector m)
    (epsilonFirst epsilonSecond : ℚ) (K B : ℕ) (history : List (Observation m)) (bits : Fin B → Bool) :
    sample first second values epsilonFirst epsilonSecond K B history bits =
      NativeImplicitTrainingHistory.sample (fun history => (first history).model)
        (fun history => (second history).model) values epsilonFirst epsilonSecond K B history bits := by
  by_cases hw : ExactSizedTrainingTransition.bitBudget (first history) (second history) values epsilonFirst epsilonSecond K ≤ B
  · have hm : ImplicitTrainingTransition.bitBudget (first history).model (second history).model values epsilonFirst epsilonSecond K ≤ B := hw
    rw [sample,dite_eq_left hw,NativeImplicitTrainingHistory.sample,dite_eq_left hm]
    exact ExactSizedTrainingTransition.sample_refines _ _ _ _ _ _ _
  · have hm : ¬ImplicitTrainingTransition.bitBudget (first history).model (second history).model values epsilonFirst epsilonSecond K ≤ B := hw
    rw [sample,dite_eq_right hw,NativeImplicitTrainingHistory.sample,dite_eq_right hm]

def run {m : ℕ} (first second : List (Observation m) → ExactSizedDraw m) (values : RationalFieldSelector m)
    (epsilonFirst epsilonSecond : ℚ) (K B T : ℕ) (bits : Fin (T * B) → Bool) (history : List (Observation m)) : List (Observation m) :=
  runBitHistory B (sample first second values epsilonFirst epsilonSecond K B) T bits history

theorem run_refines {m : ℕ} (first second : List (Observation m) → ExactSizedDraw m) (values : RationalFieldSelector m)
    (epsilonFirst epsilonSecond : ℚ) (K B T : ℕ) (bits : Fin (T * B) → Bool) (history : List (Observation m)) :
    run first second values epsilonFirst epsilonSecond K B T bits history =
      NativeImplicitTrainingHistory.run (fun history => (first history).model)
        (fun history => (second history).model) values epsilonFirst epsilonSecond K B T bits history := by
  have he : sample first second values epsilonFirst epsilonSecond K B =
      NativeImplicitTrainingHistory.sample (fun history => (first history).model)
        (fun history => (second history).model) values epsilonFirst epsilonSecond K B := by
    funext history bits
    exact sample_refines first second values epsilonFirst epsilonSecond K B history bits
  unfold run NativeImplicitTrainingHistory.run
  rw [he]

theorem sample_feasible {m : ℕ} (first second : List (Observation m) → ExactSizedDraw m)
    (values : RationalFieldSelector m) (epsilonFirst epsilonSecond : ℚ) (hFirst : 0 < epsilonFirst) (hSecond : 0 < epsilonSecond)
    (K B : ℕ) (history : List (Observation m)) (bits : Fin B → Bool) :
    Feasible ((first history).budget : ℝ) (fun field => ((sample first second values epsilonFirst epsilonSecond K B history bits).1 field : ℝ)) ∧
      Feasible ((second history).budget : ℝ) (fun field => ((sample first second values epsilonFirst epsilonSecond K B history bits).2.1 field : ℝ)) := by
  rw [sample_refines]
  exact NativeImplicitTrainingHistory.sample_feasible _ _ _ _ _ hFirst hSecond K B history bits

theorem run_feasible {m : ℕ} (first second : List (Observation m) → ExactSizedDraw m)
    (values : RationalFieldSelector m) (epsilonFirst epsilonSecond : ℚ) (hFirst : 0 < epsilonFirst) (hSecond : 0 < epsilonSecond)
    (K B : ℕ) (budgetFirst budgetSecond : ℚ) (hf : ∀ history, (first history).budget = budgetFirst)
    (hs : ∀ history, (second history).budget = budgetSecond) (T : ℕ) (bits : Fin (T * B) → Bool)
    (history : List (Observation m)) (hInitial : ∀ observation ∈ history,
      Feasible (budgetFirst : ℝ) (fun field => (observation.1 field : ℝ)) ∧
        Feasible (budgetSecond : ℝ) (fun field => (observation.2.1 field : ℝ))) :
    ∀ observation ∈ run first second values epsilonFirst epsilonSecond K B T bits history,
      Feasible (budgetFirst : ℝ) (fun field => (observation.1 field : ℝ)) ∧
        Feasible (budgetSecond : ℝ) (fun field => (observation.2.1 field : ℝ)) := by
  rw [run_refines]
  exact NativeImplicitTrainingHistory.run_feasible _ _ values epsilonFirst epsilonSecond hFirst hSecond K B
    budgetFirst budgetSecond hf hs T bits history hInitial

theorem run_mean_error_before {m : ℕ} (first second : List (Observation m) → ExactSizedDraw m)
    (values : RationalFieldSelector m) (epsilonFirst epsilonSecond : ℚ) (hFirst : 0 < epsilonFirst) (hSecond : 0 < epsilonSecond)
    (K B L : ℕ) (hWidth : ∀ history, history.length < L →
      ExactSizedTrainingTransition.bitBudget (first history) (second history) values epsilonFirst epsilonSecond K ≤ B)
    (T : ℕ) (history : List (Observation m)) (hLimit : T + history.length ≤ L)
    (test : List (Observation m) → ℝ) (hTest : ∀ past, 0 ≤ test past ∧ test past ≤ 1) :
    |(fairBitKernel (T * B)).mean (fun bits => test (run first second values epsilonFirst epsilonSecond K B T bits history)) -
      (BoundedExpectationKernel.historyRun
        (NativeImplicitTrainingHistory.idealStep (fun history => (first history).model)
          (fun history => (second history).model) values) T history).mean test| ≤
        (T : ℝ) * ((epsilonFirst : ℝ) + (epsilonSecond : ℝ) + 1 / (2 : ℝ) ^ K) := by
  simp_rw [run_refines]
  exact NativeImplicitTrainingHistory.run_mean_error_before _ _ values epsilonFirst epsilonSecond hFirst hSecond K B L
    hWidth T history hLimit test hTest

theorem scheduled_run_error {m : ℕ} (first second : List (Observation m) → ExactSizedDraw m)
    (values : RationalFieldSelector m) (accuracy : ℚ) (ha : 0 < accuracy) (B T : ℕ)
    (hWidth : ∀ history, history.length < T →
      ExactSizedTrainingTransition.bitBudget (first history) (second history) values
        (adaptiveDrawTolerance accuracy T) (adaptiveDrawTolerance accuracy T) (adaptiveFieldPrecision accuracy T) ≤ B)
    (test : List (Observation m) → ℝ) (hTest : ∀ history, 0 ≤ test history ∧ test history ≤ 1) :
    |(fairBitKernel (T * B)).mean (fun bits => test (run first second values
      (adaptiveDrawTolerance accuracy T) (adaptiveDrawTolerance accuracy T) (adaptiveFieldPrecision accuracy T) B T bits [])) -
      (BoundedExpectationKernel.historyRun
        (NativeImplicitTrainingHistory.idealStep (fun history => (first history).model)
          (fun history => (second history).model) values) T []).mean test| ≤ (accuracy : ℝ) := by
  simp_rw [run_refines]
  exact NativeImplicitTrainingHistory.scheduled_run_error _ _ values accuracy ha B T hWidth test hTest

end Blotto.ExactSizedTrainingHistory
