import Blotto.ExactSizedTrainingHistory

/-! Each adaptive round retains the two actual prepared draws once, sharing
them between the width guard and execution/fallback. The old history runner is
preserved as the exact specification. This change does not itself eliminate
history reconstruction or prove full runtime/ownership costs. -/

namespace Blotto.ExactPreparedTrainingHistory
open ImplicitLeafCounts

abbrev Observation (m : ℕ) := ImplicitTrainingTransition.Observation m

def preparedSample {m : ℕ} (preparedFirst preparedSecond : ExactSizedDraw m) (values : RationalFieldSelector m)
    (epsilonFirst epsilonSecond : ℚ) (K B : ℕ) (bits : Fin B → Bool) : Observation m :=
  if hWidth : ExactSizedTrainingTransition.bitBudget preparedFirst preparedSecond values epsilonFirst epsilonSecond K ≤ B then
    ExactSizedTrainingTransition.sample preparedFirst preparedSecond values epsilonFirst epsilonSecond K
      (fun j => bits ⟨j.val, Nat.lt_of_lt_of_le j.isLt hWidth⟩)
  else (NativeImplicitTrainingHistory.fallbackRow preparedFirst.model,
    NativeImplicitTrainingHistory.fallbackRow preparedSecond.model,values.attempt.fallbackLabel)

def sample {m : ℕ} (first second : List (Observation m) → ExactSizedDraw m) (values : RationalFieldSelector m)
    (epsilonFirst epsilonSecond : ℚ) (K B : ℕ) (history : List (Observation m)) (bits : Fin B → Bool) : Observation m :=
  let preparedFirst := first history
  let preparedSecond := second history
  preparedSample preparedFirst preparedSecond values epsilonFirst epsilonSecond K B bits

theorem sample_refines {m : ℕ} (first second : List (Observation m) → ExactSizedDraw m) (values : RationalFieldSelector m)
    (epsilonFirst epsilonSecond : ℚ) (K B : ℕ) (history : List (Observation m)) (bits : Fin B → Bool) :
    sample first second values epsilonFirst epsilonSecond K B history bits =
      ExactSizedTrainingHistory.sample first second values epsilonFirst epsilonSecond K B history bits := rfl

def run {m : ℕ} (first second : List (Observation m) → ExactSizedDraw m) (values : RationalFieldSelector m)
    (epsilonFirst epsilonSecond : ℚ) (K B T : ℕ) (bits : Fin (T * B) → Bool) (history : List (Observation m)) : List (Observation m) :=
  runBitHistory B (sample first second values epsilonFirst epsilonSecond K B) T bits history

theorem run_refines {m : ℕ} (first second : List (Observation m) → ExactSizedDraw m) (values : RationalFieldSelector m)
    (epsilonFirst epsilonSecond : ℚ) (K B T : ℕ) (bits : Fin (T * B) → Bool) (history : List (Observation m)) :
    run first second values epsilonFirst epsilonSecond K B T bits history =
      NativeImplicitTrainingHistory.run (fun history => (first history).model)
        (fun history => (second history).model) values epsilonFirst epsilonSecond K B T bits history :=
  ExactSizedTrainingHistory.run_refines first second values epsilonFirst epsilonSecond K B T bits history

theorem run_feasible {m : ℕ} (first second : List (Observation m) → ExactSizedDraw m)
    (values : RationalFieldSelector m) (epsilonFirst epsilonSecond : ℚ) (hFirst : 0 < epsilonFirst) (hSecond : 0 < epsilonSecond)
    (K B : ℕ) (budgetFirst budgetSecond : ℚ) (hf : ∀ history, (first history).budget = budgetFirst)
    (hs : ∀ history, (second history).budget = budgetSecond) (T : ℕ) (bits : Fin (T * B) → Bool)
    (history : List (Observation m)) (hInitial : ∀ observation ∈ history,
      Feasible (budgetFirst : ℝ) (fun field => (observation.1 field : ℝ)) ∧
        Feasible (budgetSecond : ℝ) (fun field => (observation.2.1 field : ℝ))) :
    ∀ observation ∈ run first second values epsilonFirst epsilonSecond K B T bits history,
      Feasible (budgetFirst : ℝ) (fun field => (observation.1 field : ℝ)) ∧
        Feasible (budgetSecond : ℝ) (fun field => (observation.2.1 field : ℝ)) :=
  ExactSizedTrainingHistory.run_feasible first second values epsilonFirst epsilonSecond hFirst hSecond K B
    budgetFirst budgetSecond hf hs T bits history hInitial

end Blotto.ExactPreparedTrainingHistory
