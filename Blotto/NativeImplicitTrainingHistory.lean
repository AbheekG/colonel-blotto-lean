import Blotto.ImplicitTrainingTransition
import Blotto.NativeSamplingSchedule

/-! Actual fixed-block adaptive training uses stored implicit whole-row draws.
Overflow returns stored feasible fallback rows. Before the proved horizon cap,
fresh-block errors accumulate unconditionally. Concrete Gibbs/convergence and
source-cap instantiation remain separate callers. -/

namespace Blotto.NativeImplicitTrainingHistory
open ImplicitLeafCounts
open scoped Classical

abbrev Observation (m : ℕ) := ImplicitTrainingTransition.Observation m

def fallbackRow {m : ℕ} (prepared : SizedImplicitSampler m) : Fin m → ℚ :=
  prepared.reindex (prepared.stored.tree.decodeLabel prepared.stored.nonnegative prepared.stored.fallback)

theorem fallbackRow_feasible {m : ℕ} (prepared : SizedImplicitSampler m) :
    Feasible (prepared.budget : ℝ) (fun field => (fallbackRow prepared field : ℝ)) := by
  have hNonnegative := (prepared.stored.tree.allocationTree prepared.stored.nonnegative).decode_nonnegative
    (prepared.stored.fallback.cast (prepared.stored.tree.allocationTree_labels prepared.stored.nonnegative).symm)
  have hSum := prepared.stored.tree.decodeLabel_resource prepared.stored.nonnegative prepared.stored.fallback
  constructor
  · intro field
    change (0 : ℝ) ≤ ((prepared.stored.tree.allocationTree prepared.stored.nonnegative).decode
      (prepared.stored.fallback.cast (prepared.stored.tree.allocationTree_labels prepared.stored.nonnegative).symm)
      (field.cast prepared.fields.symm) : ℝ)
    exact_mod_cast hNonnegative (field.cast prepared.fields.symm)
  · have hReindex := Equiv.sum_comp (finCongr prepared.fields.symm)
      (fun field => (prepared.stored.tree.decodeLabel prepared.stored.nonnegative prepared.stored.fallback field : ℝ))
    exact hReindex.trans_le (hSum.trans_le prepared.stored.fallback_feasible)

def sample {m : ℕ} (first second : List (Observation m) → SizedImplicitSampler m) (values : RationalFieldSelector m)
    (epsilonFirst epsilonSecond : ℚ) (K B : ℕ) (history : List (Observation m)) (bits : Fin B → Bool) : Observation m :=
  if hWidth : ImplicitTrainingTransition.bitBudget (first history) (second history) values epsilonFirst epsilonSecond K ≤ B then
    ImplicitTrainingTransition.sample (first history) (second history) values epsilonFirst epsilonSecond K
      (fun j => bits ⟨j.val, Nat.lt_of_lt_of_le j.isLt hWidth⟩)
  else (fallbackRow (first history), fallbackRow (second history), values.attempt.fallbackLabel)

noncomputable def idealStep {m : ℕ} (first second : List (Observation m) → SizedImplicitSampler m)
    (values : RationalFieldSelector m) (history : List (Observation m)) : BoundedExpectationKernel (Observation m) :=
  ImplicitTrainingTransition.idealKernel (first history) (second history) values

theorem step_close_before {m : ℕ} (first second : List (Observation m) → SizedImplicitSampler m)
    (values : RationalFieldSelector m) (epsilonFirst epsilonSecond : ℚ) (hFirst : 0 < epsilonFirst) (hSecond : 0 < epsilonSecond)
    (K B L : ℕ) (hWidth : ∀ history, history.length < L →
      ImplicitTrainingTransition.bitBudget (first history) (second history) values epsilonFirst epsilonSecond K ≤ B)
    (history : List (Observation m)) (hLength : history.length < L) :
    (bitHistoryStep B (sample first second values epsilonFirst epsilonSecond K B) history).Close
      (idealStep first second values history) ((epsilonFirst : ℝ) + (epsilonSecond : ℝ) + 1 / (2 : ℝ) ^ K) := by
  intro test hTest
  have hFit := hWidth history hLength
  change |(fairBitKernel B).mean (fun bits => test (sample first second values epsilonFirst epsilonSecond K B history bits)) - _| ≤ _
  unfold sample
  simp only [hFit, dite_true]
  have hp := fairBitKernel_prefix_mean
    (ImplicitTrainingTransition.bitBudget (first history) (second history) values epsilonFirst epsilonSecond K) B hFit
    (fun bits => test (ImplicitTrainingTransition.sample (first history) (second history) values epsilonFirst epsilonSecond K bits))
  rw [hp]
  rw [ImplicitTrainingTransition.sample_mean]
  exact ImplicitTrainingTransition.kernel_close (first history) (second history) values epsilonFirst epsilonSecond hFirst hSecond K test hTest

def run {m : ℕ} (first second : List (Observation m) → SizedImplicitSampler m) (values : RationalFieldSelector m)
    (epsilonFirst epsilonSecond : ℚ) (K B T : ℕ) (bits : Fin (T * B) → Bool) (history : List (Observation m)) : List (Observation m) :=
  runBitHistory B (sample first second values epsilonFirst epsilonSecond K B) T bits history

theorem run_mean_error_before {m : ℕ} (first second : List (Observation m) → SizedImplicitSampler m)
    (values : RationalFieldSelector m) (epsilonFirst epsilonSecond : ℚ) (hFirst : 0 < epsilonFirst) (hSecond : 0 < epsilonSecond)
    (K B L : ℕ) (hWidth : ∀ history, history.length < L →
      ImplicitTrainingTransition.bitBudget (first history) (second history) values epsilonFirst epsilonSecond K ≤ B)
    (T : ℕ) (history : List (Observation m)) (hLimit : T + history.length ≤ L)
    (test : List (Observation m) → ℝ) (hTest : ∀ past, 0 ≤ test past ∧ test past ≤ 1) :
    |(fairBitKernel (T * B)).mean (fun bits => test (run first second values epsilonFirst epsilonSecond K B T bits history)) -
      (BoundedExpectationKernel.historyRun (idealStep first second values) T history).mean test| ≤
        (T : ℝ) * ((epsilonFirst : ℝ) + (epsilonSecond : ℝ) + 1 / (2 : ℝ) ^ K) :=
  runBitHistory_bounded_error_before B _ _ _ (by
    have ha : (0 : ℝ) < epsilonFirst := by exact_mod_cast hFirst
    have hb : (0 : ℝ) < epsilonSecond := by exact_mod_cast hSecond
    positivity) L (step_close_before first second values epsilonFirst epsilonSecond hFirst hSecond K B L hWidth)
      T history hLimit test hTest

theorem sample_feasible {m : ℕ} (first second : List (Observation m) → SizedImplicitSampler m)
    (values : RationalFieldSelector m) (epsilonFirst epsilonSecond : ℚ) (hFirst : 0 < epsilonFirst) (hSecond : 0 < epsilonSecond)
    (K B : ℕ) (history : List (Observation m)) (bits : Fin B → Bool) :
    Feasible ((first history).budget : ℝ) (fun field => ((sample first second values epsilonFirst epsilonSecond K B history bits).1 field : ℝ)) ∧
      Feasible ((second history).budget : ℝ) (fun field => ((sample first second values epsilonFirst epsilonSecond K B history bits).2.1 field : ℝ)) := by
  unfold sample
  split
  · exact ImplicitTrainingTransition.sample_feasible _ _ _ _ _ hFirst hSecond _ _
  · exact ⟨fallbackRow_feasible (first history), fallbackRow_feasible (second history)⟩

theorem run_feasible {m : ℕ} (first second : List (Observation m) → SizedImplicitSampler m)
    (values : RationalFieldSelector m) (epsilonFirst epsilonSecond : ℚ) (hFirst : 0 < epsilonFirst) (hSecond : 0 < epsilonSecond)
    (K B : ℕ) (budgetFirst budgetSecond : ℚ) (hf : ∀ history, (first history).budget = budgetFirst)
    (hs : ∀ history, (second history).budget = budgetSecond) (T : ℕ) (bits : Fin (T * B) → Bool)
    (history : List (Observation m)) (hInitial : ∀ observation ∈ history,
      Feasible (budgetFirst : ℝ) (fun field => (observation.1 field : ℝ)) ∧
        Feasible (budgetSecond : ℝ) (fun field => (observation.2.1 field : ℝ))) :
    ∀ observation ∈ run first second values epsilonFirst epsilonSecond K B T bits history,
      Feasible (budgetFirst : ℝ) (fun field => (observation.1 field : ℝ)) ∧
        Feasible (budgetSecond : ℝ) (fun field => (observation.2.1 field : ℝ)) := by
  induction T generalizing history with
  | zero => exact hInitial
  | succ T ih =>
    unfold run runBitHistory
    apply ih
    intro observation hMem
    rcases List.mem_cons.mp hMem with rfl | hMem
    · have he := sample_feasible first second values epsilonFirst epsilonSecond hFirst hSecond K B history
        (firstBitBlock B (T * B) (fun j => bits (j.cast (by ring))))
      rw [hf, hs] at he
      exact he
    · exact hInitial observation hMem

theorem scheduled_run_error {m : ℕ} (first second : List (Observation m) → SizedImplicitSampler m)
    (values : RationalFieldSelector m) (accuracy : ℚ) (ha : 0 < accuracy) (B T : ℕ)
    (hWidth : ∀ history, history.length < T →
      ImplicitTrainingTransition.bitBudget (first history) (second history) values
        (adaptiveDrawTolerance accuracy T) (adaptiveDrawTolerance accuracy T) (adaptiveFieldPrecision accuracy T) ≤ B)
    (test : List (Observation m) → ℝ) (hTest : ∀ history, 0 ≤ test history ∧ test history ≤ 1) :
    |(fairBitKernel (T * B)).mean (fun bits => test (run first second values
      (adaptiveDrawTolerance accuracy T) (adaptiveDrawTolerance accuracy T) (adaptiveFieldPrecision accuracy T) B T bits [])) -
      (BoundedExpectationKernel.historyRun (idealStep first second values) T []).mean test| ≤ (accuracy : ℝ) := by
  have he := run_mean_error_before first second values (adaptiveDrawTolerance accuracy T) (adaptiveDrawTolerance accuracy T)
    (adaptiveDrawTolerance_positive accuracy ha T) (adaptiveDrawTolerance_positive accuracy ha T)
    (adaptiveFieldPrecision accuracy T) B T hWidth T [] (by simp) test hTest
  exact he.trans (by simpa only [two_mul] using adaptiveTotalDrawError accuracy ha T)

end Blotto.NativeImplicitTrainingHistory
