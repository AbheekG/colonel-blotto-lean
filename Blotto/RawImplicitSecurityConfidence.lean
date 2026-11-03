import Blotto.RawImplicitSecurityState
import Blotto.NativeImplicitTrainingHistory
import Blotto.ProductRawSecuritySimulation

/-! The actual succinct raw-history trainer has exactly the retained current
Gibbs conditional law and finite indexed confidence bound. This module exposes
the horizon cap until the separately derived source cap is composed; the finite
security game is not a continuous-output certification theorem. -/

namespace Blotto
open scoped BigOperators Classical
namespace ProductSecurityTrainer

noncomputable def compactIdealStep {n : ℕ} (c : ProductSecurityTrainer (n + 1)) (cfg : c.ImplicitCodeConfig)
    (history : List (RawObservation (n + 1))) : BoundedExpectationKernel (RawObservation (n + 1)) :=
  NativeImplicitTrainingHistory.idealStep (c.compactPreparedA cfg) (c.compactPreparedB cfg) c.values history

theorem compactIdealStep_mean {n : ℕ} (c : ProductSecurityTrainer (n + 1)) (cfg : c.ImplicitCodeConfig)
    (history : List (RawObservation (n + 1))) (test : RawObservation (n + 1) → ℝ) :
    (c.compactIdealStep cfg history).mean test = (c.rawIdealStep history).mean test := by
  change (c.compactPreparedA cfg history).targetKernel.mean
    (fun rowA => (c.compactPreparedB cfg history).targetKernel.mean
      (fun rowB => ∑ field, (c.values.weight field : ℝ) * test (rowA, rowB, field))) = _
  rw [c.compactPreparedA_target_mean]
  apply congrArg (c.rawPreparedA history).rationalTargetKernel.mean
  funext rowA
  exact c.compactPreparedB_target_mean cfg history _

theorem compactIdealHistory_mean {n : ℕ} (c : ProductSecurityTrainer (n + 1)) (cfg : c.ImplicitCodeConfig)
    (T : ℕ) (test : List (RawObservation (n + 1)) → ℝ) :
    (BoundedExpectationKernel.historyRun (c.compactIdealStep cfg) T []).mean test =
      SparseMW.historyMean c.transition T (fun history => test (history.map c.encodeObservation)) :=
  finiteHistory_encoded_mean c.transition c.transition_nonnegative c.transition_sum (c.compactIdealStep cfg)
    c.encodeObservation (fun history test =>
      ((c.compactIdealStep_mean cfg (history.map c.encodeObservation) test).trans
        (c.rawIdealStep_encoded_mean history test)).symm) T test

def compactNativeRun {n : ℕ} (c : ProductSecurityTrainer (n + 1)) (cfg : c.ImplicitCodeConfig) (epsilonA epsilonB : ℚ)
    (K B T : ℕ) (bits : Fin (T * B) → Bool) : List (RawObservation (n + 1)) :=
  NativeImplicitTrainingHistory.run (c.compactPreparedA cfg) (c.compactPreparedB cfg) c.values epsilonA epsilonB K B T bits []

theorem compactNativeRun_feasible {n : ℕ} (c : ProductSecurityTrainer (n + 1)) (cfg : c.ImplicitCodeConfig) (epsilonA epsilonB : ℚ)
    (hA : 0 < epsilonA) (hB : 0 < epsilonB) (K B T : ℕ) (bits : Fin (T * B) → Bool) :
    ∀ observation ∈ c.compactNativeRun cfg epsilonA epsilonB K B T bits,
      Feasible (c.budgetA : ℝ) (fun field => (observation.1 field : ℝ)) ∧
        Feasible (c.budgetB : ℝ) (fun field => (observation.2.1 field : ℝ)) :=
  NativeImplicitTrainingHistory.run_feasible (c.compactPreparedA cfg) (c.compactPreparedB cfg) c.values epsilonA epsilonB hA hB K B
    c.budgetA c.budgetB (c.compactPreparedA_budget cfg) (c.compactPreparedB_budget cfg) T bits [] (by simp)

theorem compactNativeRun_bounded_error {n : ℕ} (c : ProductSecurityTrainer (n + 1)) (cfg : c.ImplicitCodeConfig)
    (epsilonA epsilonB : ℚ) (hA : 0 < epsilonA) (hB : 0 < epsilonB) (K B T : ℕ)
    (hWidth : ∀ history, history.length < T →
      ImplicitTrainingTransition.bitBudget ((c.compactPreparedA cfg) history) ((c.compactPreparedB cfg) history) c.values epsilonA epsilonB K ≤ B)
    (test : List (RawObservation (n + 1)) → ℝ) (hTest : ∀ history, 0 ≤ test history ∧ test history ≤ 1) :
    |(fairBitKernel (T * B)).mean (fun bits => test (c.compactNativeRun cfg epsilonA epsilonB K B T bits)) -
      SparseMW.historyMean c.transition T (fun history => test (history.map c.encodeObservation))| ≤
        (T : ℝ) * ((epsilonA : ℝ) + (epsilonB : ℝ) + 1 / (2 : ℝ) ^ K) := by
  have he := NativeImplicitTrainingHistory.run_mean_error_before (c.compactPreparedA cfg) (c.compactPreparedB cfg) c.values
    epsilonA epsilonB hA hB K B T hWidth T [] (by simp) test hTest
  change |(fairBitKernel (T * B)).mean (fun bits => test (c.compactNativeRun cfg epsilonA epsilonB K B T bits)) -
    (BoundedExpectationKernel.historyRun (c.compactIdealStep cfg) T []).mean test| ≤ _ at he
  rw [c.compactIdealHistory_mean cfg] at he
  exact he

theorem compactNativeRun_scheduled_error {n : ℕ} (c : ProductSecurityTrainer (n + 1)) (cfg : c.ImplicitCodeConfig)
    (accuracy : ℚ) (ha : 0 < accuracy) (T B : ℕ)
    (hWidth : ∀ history, history.length < T →
      ImplicitTrainingTransition.bitBudget ((c.compactPreparedA cfg) history) ((c.compactPreparedB cfg) history) c.values
        (adaptiveDrawTolerance accuracy T) (adaptiveDrawTolerance accuracy T) (adaptiveFieldPrecision accuracy T) ≤ B)
    (test : List (RawObservation (n + 1)) → ℝ) (hTest : ∀ history, 0 ≤ test history ∧ test history ≤ 1) :
    |(fairBitKernel (T * B)).mean (fun bits => test (c.compactNativeRun cfg
      (adaptiveDrawTolerance accuracy T) (adaptiveDrawTolerance accuracy T) (adaptiveFieldPrecision accuracy T) B T bits)) -
      SparseMW.historyMean c.transition T (fun history => test (history.map c.encodeObservation))| ≤ (accuracy : ℝ) := by
  have he := c.compactNativeRun_bounded_error cfg (adaptiveDrawTolerance accuracy T) (adaptiveDrawTolerance accuracy T)
    (adaptiveDrawTolerance_positive accuracy ha T) (adaptiveDrawTolerance_positive accuracy ha T)
    (adaptiveFieldPrecision accuracy T) B T hWidth test hTest
  exact he.trans (by simpa only [two_mul] using adaptiveTotalDrawError accuracy ha T)

theorem compactNativeRun_event_error {n : ℕ} (c : ProductSecurityTrainer (n + 1)) (cfg : c.ImplicitCodeConfig)
    (accuracy : ℚ) (ha : 0 < accuracy) (T B : ℕ)
    (hWidth : ∀ history, history.length < T →
      ImplicitTrainingTransition.bitBudget ((c.compactPreparedA cfg) history) ((c.compactPreparedB cfg) history) c.values
        (adaptiveDrawTolerance accuracy T) (adaptiveDrawTolerance accuracy T) (adaptiveFieldPrecision accuracy T) ≤ B)
    (event : Set (List (RawObservation (n + 1)))) :
    |(fairBitKernel (T * B)).mean (fun bits => if c.compactNativeRun cfg
      (adaptiveDrawTolerance accuracy T) (adaptiveDrawTolerance accuracy T) (adaptiveFieldPrecision accuracy T) B T bits ∈ event then 1 else 0) -
      SparseMW.historyMean c.transition T (fun history => if history.map c.encodeObservation ∈ event then 1 else 0)| ≤ (accuracy : ℝ) :=
  c.compactNativeRun_scheduled_error cfg accuracy ha T B hWidth (fun history => if history ∈ event then 1 else 0)
    (fun history => by split_ifs <;> norm_num)

theorem compactNativeRun_bad_gap_bound {n : ℕ} (c : ProductSecurityTrainer (n + 1)) (cfg : c.ImplicitCodeConfig)
    (accuracy : ℚ) (ha : 0 < accuracy) (T B : ℕ)
    (hWidth : ∀ history, history.length < T →
      ImplicitTrainingTransition.bitBudget ((c.compactPreparedA cfg) history) ((c.compactPreparedB cfg) history) c.values
        (adaptiveDrawTolerance accuracy T) (adaptiveDrawTolerance accuracy T) (adaptiveFieldPrecision accuracy T) ≤ B)
    (threshold : ℝ) :
    (fairBitKernel (T * B)).mean (fun bits => if threshold < c.rawGap (c.compactNativeRun cfg
      (adaptiveDrawTolerance accuracy T) (adaptiveDrawTolerance accuracy T) (adaptiveFieldPrecision accuracy T) B T bits)
      then 1 else 0) ≤ c.badGapMean T threshold + (accuracy : ℝ) := by
  have he := c.compactNativeRun_event_error cfg accuracy ha T B hWidth {history | threshold < c.rawGap history}
  simp only [Set.mem_ofPred_eq, rawGap_encoded] at he
  change |(fairBitKernel (T * B)).mean (fun bits => if threshold < c.rawGap (c.compactNativeRun cfg
    (adaptiveDrawTolerance accuracy T) (adaptiveDrawTolerance accuracy T) (adaptiveFieldPrecision accuracy T) B T bits)
      then 1 else 0) - c.badGapMean T threshold| ≤ (accuracy : ℝ) at he
  linarith [(le_abs_self ((fairBitKernel (T * B)).mean (fun bits => if threshold < c.rawGap (c.compactNativeRun cfg
    (adaptiveDrawTolerance accuracy T) (adaptiveDrawTolerance accuracy T) (adaptiveFieldPrecision accuracy T) B T bits)
      then 1 else 0) - c.badGapMean T threshold))]


end ProductSecurityTrainer
end Blotto
