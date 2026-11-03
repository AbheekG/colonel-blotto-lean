import Blotto.ProductRawSecurityState
import Blotto.AdaptiveKernelSimulation
import Blotto.NativeSamplingSchedule
import Blotto.ProductSecurityConfidence

/-! The actual adaptive rational sampler refines the concrete labelled security
trainer. The ideal next-law equality is derived from the updated Gibbs fields;
duplicate row encodings are allowed. A horizon-local bit cap is still explicit,
and these finite-training laws do not claim continuous output certification. -/

namespace Blotto
open scoped BigOperators Classical
namespace ProductSecurityTrainer

noncomputable def rawIdealStep {n : ℕ} (c : ProductSecurityTrainer (n + 1))
    (history : List (RawObservation (n + 1))) : BoundedExpectationKernel (RawObservation (n + 1)) :=
  NativePreparedTrainingHistory.idealStep c.rawPreparedA c.rawPreparedB c.values history

theorem rawIdealStep_encoded_mean {n : ℕ} (c : ProductSecurityTrainer (n + 1))
    (history : List (Fin c.observations)) (test : RawObservation (n + 1) → ℝ) :
    (c.rawIdealStep (history.map c.encodeObservation)).mean test =
      (finiteTransitionKernel c.transition c.transition_nonnegative c.transition_sum history).mean
        (fun x => test (c.encodeObservation x)) := by
  change (c.rawPreparedA (history.map c.encodeObservation)).rationalTargetKernel.mean
    (fun rowA => (c.rawPreparedB (history.map c.encodeObservation)).rationalTargetKernel.mean
      (fun rowB => ∑ field, (c.values.weight field : ℝ) * test (rowA, rowB, field))) = _
  rw [c.rawPreparedA_encoded_mean]
  simp_rw [c.rawPreparedB_encoded_mean]
  change (∑ i, (c.lawA history).realWeight i *
    (∑ j, (c.lawB history).realWeight j *
      (∑ field, (c.values.weight field : ℝ) * test ((c.lawA history).row i, (c.lawB history).row j, field)))) =
    ∑ x : Fin (c.actionsA * (c.actionsB * (n + 1))), c.transition history x * test (c.encodeObservation x)
  rw [← Equiv.sum_comp (ProductFiniteTraining.observationEquiv c.actionsA c.actionsB (n + 1))]
  simp only [transition, ProductFiniteTraining.indexedProbability, Equiv.symm_apply_apply,
    encodeObservation, observed, Fintype.sum_prod_type]
  simp only [ProductFiniteTraining.probability, Rat.cast_mul]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro field _
  change (c.lawA history).realWeight i * ((c.lawB history).realWeight j *
    ((c.values.weight field : ℝ) * test ((c.lawA history).row i, (c.lawB history).row j, field))) = _
  rw [mul_assoc, mul_assoc]
  rfl

theorem rawIdealHistory_mean {n : ℕ} (c : ProductSecurityTrainer (n + 1))
    (T : ℕ) (test : List (RawObservation (n + 1)) → ℝ) :
    (BoundedExpectationKernel.historyRun c.rawIdealStep T []).mean test =
      SparseMW.historyMean c.transition T (fun history => test (history.map c.encodeObservation)) :=
  finiteHistory_encoded_mean c.transition c.transition_nonnegative c.transition_sum c.rawIdealStep
    c.encodeObservation (fun history test => (c.rawIdealStep_encoded_mean history test).symm) T test

def rawNativeRun {n : ℕ} (c : ProductSecurityTrainer (n + 1)) (epsilonA epsilonB : ℚ)
    (K B T : ℕ) (bits : Fin (T * B) → Bool) : List (RawObservation (n + 1)) :=
  NativePreparedTrainingHistory.run c.rawPreparedA c.rawPreparedB c.values epsilonA epsilonB K B T bits []

theorem rawNativeRun_feasible {n : ℕ} (c : ProductSecurityTrainer (n + 1)) (epsilonA epsilonB : ℚ)
    (K B T : ℕ) (bits : Fin (T * B) → Bool) :
    ∀ observation ∈ c.rawNativeRun epsilonA epsilonB K B T bits,
      Feasible (c.budgetA : ℝ) (fun field => (observation.1 field : ℝ)) ∧
        Feasible (c.budgetB : ℝ) (fun field => (observation.2.1 field : ℝ)) :=
  NativePreparedTrainingHistory.run_feasible c.rawPreparedA c.rawPreparedB c.values epsilonA epsilonB K B
    c.budgetA c.budgetB c.rawPreparedA_budget c.rawPreparedB_budget T bits [] (by simp)

theorem rawNativeRun_bounded_error {n : ℕ} (c : ProductSecurityTrainer (n + 1))
    (epsilonA epsilonB : ℚ) (hA : 0 < epsilonA) (hB : 0 < epsilonB) (K B T : ℕ)
    (hWidth : ∀ history, history.length < T →
      PreparedProductTransition.bitBudget (c.rawPreparedA history) (c.rawPreparedB history) c.values epsilonA epsilonB K ≤ B)
    (test : List (RawObservation (n + 1)) → ℝ) (hTest : ∀ history, 0 ≤ test history ∧ test history ≤ 1) :
    |(fairBitKernel (T * B)).mean (fun bits => test (c.rawNativeRun epsilonA epsilonB K B T bits)) -
      SparseMW.historyMean c.transition T (fun history => test (history.map c.encodeObservation))| ≤
        (T : ℝ) * ((epsilonA : ℝ) + (epsilonB : ℝ) + 1 / (2 : ℝ) ^ K) := by
  have he := NativePreparedTrainingHistory.run_bounded_error_before c.rawPreparedA c.rawPreparedB c.values
    epsilonA epsilonB hA hB K B T hWidth T [] (by simp) test hTest
  change |(fairBitKernel (T * B)).mean (fun bits => test (c.rawNativeRun epsilonA epsilonB K B T bits)) -
    (BoundedExpectationKernel.historyRun c.rawIdealStep T []).mean test| ≤ _ at he
  rw [c.rawIdealHistory_mean] at he
  exact he

theorem rawNativeRun_scheduled_error {n : ℕ} (c : ProductSecurityTrainer (n + 1))
    (accuracy : ℚ) (ha : 0 < accuracy) (T B : ℕ)
    (hWidth : ∀ history, history.length < T →
      PreparedProductTransition.bitBudget (c.rawPreparedA history) (c.rawPreparedB history) c.values
        (adaptiveDrawTolerance accuracy T) (adaptiveDrawTolerance accuracy T) (adaptiveFieldPrecision accuracy T) ≤ B)
    (test : List (RawObservation (n + 1)) → ℝ) (hTest : ∀ history, 0 ≤ test history ∧ test history ≤ 1) :
    |(fairBitKernel (T * B)).mean (fun bits => test (c.rawNativeRun
      (adaptiveDrawTolerance accuracy T) (adaptiveDrawTolerance accuracy T) (adaptiveFieldPrecision accuracy T) B T bits)) -
      SparseMW.historyMean c.transition T (fun history => test (history.map c.encodeObservation))| ≤ (accuracy : ℝ) := by
  have he := c.rawNativeRun_bounded_error (adaptiveDrawTolerance accuracy T) (adaptiveDrawTolerance accuracy T)
    (adaptiveDrawTolerance_positive accuracy ha T) (adaptiveDrawTolerance_positive accuracy ha T)
    (adaptiveFieldPrecision accuracy T) B T hWidth test hTest
  exact he.trans (by simpa only [two_mul] using adaptiveTotalDrawError accuracy ha T)

theorem rawNativeRun_event_error {n : ℕ} (c : ProductSecurityTrainer (n + 1))
    (accuracy : ℚ) (ha : 0 < accuracy) (T B : ℕ)
    (hWidth : ∀ history, history.length < T →
      PreparedProductTransition.bitBudget (c.rawPreparedA history) (c.rawPreparedB history) c.values
        (adaptiveDrawTolerance accuracy T) (adaptiveDrawTolerance accuracy T) (adaptiveFieldPrecision accuracy T) ≤ B)
    (event : Set (List (RawObservation (n + 1)))) :
    |(fairBitKernel (T * B)).mean (fun bits => if c.rawNativeRun
      (adaptiveDrawTolerance accuracy T) (adaptiveDrawTolerance accuracy T) (adaptiveFieldPrecision accuracy T) B T bits ∈ event then 1 else 0) -
      SparseMW.historyMean c.transition T (fun history => if history.map c.encodeObservation ∈ event then 1 else 0)| ≤ (accuracy : ℝ) :=
  c.rawNativeRun_scheduled_error accuracy ha T B hWidth (fun history => if history ∈ event then 1 else 0)
    (fun history => by split_ifs <;> norm_num)

noncomputable def rawLawA {m : ℕ} (c : ProductSecurityTrainer m) (history : List (RawObservation m)) :
    RationalWholeRowLaw c.actionsA m :=
  SparseMW.gibbsWholeRowLaw c.bidsA c.budgetA c.fallbackA c.fallbackA_feasible
    (c.rawFieldsA history) (c.rawFieldsA_positive history)

noncomputable def rawLawB {m : ℕ} (c : ProductSecurityTrainer m) (history : List (RawObservation m)) :
    RationalWholeRowLaw c.actionsB m :=
  SparseMW.gibbsWholeRowLaw c.bidsB c.budgetB c.fallbackB c.fallbackB_feasible
    (c.rawFieldsB history) (c.rawFieldsB_positive history)

theorem rawLawA_encoded {m : ℕ} (c : ProductSecurityTrainer m) (history : List (Fin c.observations)) :
    c.rawLawA (history.map c.encodeObservation) = c.lawA history := by
  unfold rawLawA
  simp only [rawFieldsA_encoded]
  rfl

theorem rawLawB_encoded {m : ℕ} (c : ProductSecurityTrainer m) (history : List (Fin c.observations)) :
    c.rawLawB (history.map c.encodeObservation) = c.lawB history := by
  unfold rawLawB
  simp only [rawFieldsB_encoded]
  rfl

noncomputable def rawHistoryVectorSum {m r : ℕ}
    (probability : List (RawObservation m) → Fin r → ℝ) : List (RawObservation m) → Fin r → ℝ
  | [] => fun _ => 0
  | _x :: history => fun i => rawHistoryVectorSum probability history i + probability history i

noncomputable def rawHistoryAverage {m r : ℕ}
    (probability : List (RawObservation m) → Fin r → ℝ) (history : List (RawObservation m)) : Fin r → ℝ :=
  fun i => rawHistoryVectorSum probability history i / history.length

theorem rawHistoryAverage_encoded {m r : ℕ} (c : ProductSecurityTrainer m)
    (probability : List (RawObservation m) → Fin r → ℝ)
    (history : List (Fin c.observations)) :
    rawHistoryAverage probability (history.map c.encodeObservation) =
      FiniteSaddle.historyAverage (fun past => probability (past.map c.encodeObservation)) history := by
  have hs : rawHistoryVectorSum probability (history.map c.encodeObservation) =
      FiniteSaddle.historyVectorSum (fun past => probability (past.map c.encodeObservation)) history := by
    induction history with
    | nil => rfl
    | cons x history ih =>
      simp only [List.map_cons, rawHistoryVectorSum, FiniteSaddle.historyVectorSum, ih]
  unfold rawHistoryAverage FiniteSaddle.historyAverage
  rw [hs, List.length_map]

noncomputable def rawGap {m : ℕ} (c : ProductSecurityTrainer m) (history : List (RawObservation m)) : ℝ :=
  FiniteSaddle.GapAt c.matrix (rawHistoryAverage (fun past => (c.rawLawA past).realWeight) history)
    (rawHistoryAverage (fun past => (c.rawLawB past).realWeight) history)
    (FiniteSaddle.minimizingRow c.actionsA_positive c.matrix
      (rawHistoryAverage (fun past => (c.rawLawB past).realWeight) history))
    (FiniteSaddle.maximizingColumn c.actionsB_positive c.matrix
      (rawHistoryAverage (fun past => (c.rawLawA past).realWeight) history))

theorem rawGap_encoded {m : ℕ} (c : ProductSecurityTrainer m) (history : List (Fin c.observations)) :
    c.rawGap (history.map c.encodeObservation) = c.gap history := by
  unfold rawGap gap
  simp only [rawHistoryAverage_encoded, rawLawA_encoded, rawLawB_encoded]

theorem rawNativeRun_bad_gap_bound {n : ℕ} (c : ProductSecurityTrainer (n + 1))
    (accuracy : ℚ) (ha : 0 < accuracy) (T B : ℕ)
    (hWidth : ∀ history, history.length < T →
      PreparedProductTransition.bitBudget (c.rawPreparedA history) (c.rawPreparedB history) c.values
        (adaptiveDrawTolerance accuracy T) (adaptiveDrawTolerance accuracy T) (adaptiveFieldPrecision accuracy T) ≤ B)
    (threshold : ℝ) :
    (fairBitKernel (T * B)).mean (fun bits => if threshold < c.rawGap (c.rawNativeRun
      (adaptiveDrawTolerance accuracy T) (adaptiveDrawTolerance accuracy T) (adaptiveFieldPrecision accuracy T) B T bits)
      then 1 else 0) ≤ c.badGapMean T threshold + (accuracy : ℝ) := by
  have he := c.rawNativeRun_event_error accuracy ha T B hWidth {history | threshold < c.rawGap history}
  simp only [Set.mem_ofPred_eq, rawGap_encoded] at he
  change |(fairBitKernel (T * B)).mean (fun bits => if threshold < c.rawGap (c.rawNativeRun
    (adaptiveDrawTolerance accuracy T) (adaptiveDrawTolerance accuracy T) (adaptiveFieldPrecision accuracy T) B T bits)
      then 1 else 0) - c.badGapMean T threshold| ≤ (accuracy : ℝ) at he
  linarith [(le_abs_self ((fairBitKernel (T * B)).mean (fun bits => if threshold < c.rawGap (c.rawNativeRun
    (adaptiveDrawTolerance accuracy T) (adaptiveDrawTolerance accuracy T) (adaptiveFieldPrecision accuracy T) B T bits)
      then 1 else 0) - c.badGapMean T threshold))]

theorem withAccuracy_rawNative_bad_gap_bound {n : ℕ} (c : ProductSecurityTrainer (n + 1))
    (epsilon entropy accuracy : ℚ) (he : 0 < epsilon ∧ epsilon ≤ 1) (hJ : 0 ≤ entropy)
    (hEntropy : Real.log c.actionsA + Real.log c.actionsB ≤ (entropy : ℝ)) (ha : 0 < accuracy) (B : ℕ)
    (hWidth : ∀ history, history.length < trainingRounds (epsilon / 2048) epsilon entropy →
      PreparedProductTransition.bitBudget ((c.withAccuracy epsilon he).rawPreparedA history)
        ((c.withAccuracy epsilon he).rawPreparedB history) c.values
        (adaptiveDrawTolerance accuracy (trainingRounds (epsilon / 2048) epsilon entropy))
        (adaptiveDrawTolerance accuracy (trainingRounds (epsilon / 2048) epsilon entropy))
        (adaptiveFieldPrecision accuracy (trainingRounds (epsilon / 2048) epsilon entropy)) ≤ B) :
    (fairBitKernel (trainingRounds (epsilon / 2048) epsilon entropy * B)).mean (fun bits => if
      (epsilon : ℝ) / 8 < (c.withAccuracy epsilon he).rawGap ((c.withAccuracy epsilon he).rawNativeRun
        (adaptiveDrawTolerance accuracy (trainingRounds (epsilon / 2048) epsilon entropy))
        (adaptiveDrawTolerance accuracy (trainingRounds (epsilon / 2048) epsilon entropy))
        (adaptiveFieldPrecision accuracy (trainingRounds (epsilon / 2048) epsilon entropy)) B
        (trainingRounds (epsilon / 2048) epsilon entropy) bits) then 1 else 0) ≤ 1 / 16 + (accuracy : ℝ) := by
  have hn := (c.withAccuracy epsilon he).rawNativeRun_bad_gap_bound accuracy ha
    (trainingRounds (epsilon / 2048) epsilon entropy) B hWidth ((epsilon : ℝ) / 8)
  exact hn.trans (add_le_add (c.withAccuracy_bad_gap_bound epsilon entropy he hJ hEntropy) (le_refl (accuracy : ℝ)))

end ProductSecurityTrainer
end Blotto
