import Blotto.FareyPreparedDirectAccess
import Blotto.FareySourceTraining
import Blotto.ExactPreparedTrainingHistory

/-! Concrete source parameters now drive the direct Farey history sampler
inside the actual fixed-block trainer. Decoder, width, entropy, horizon and
seed-cap premises are derived from the retained source construction. Exact
every-seed execution transfers finite-security confidence. Continuous compiler,
output certification and complete runtime/space prices remain separate. -/

namespace Blotto.FareySourceTraining
open Farey ImplicitLeafCounts ProductSecurityTrainer

def Input.directBase {n : ℕ} (input : Input (n + 1)) (epsilon : ℚ) : FareyImplicitTrainer.DirectInput (n + 1) where
  first := sourceCandidateUniverse input.q (n + 1) (quantileCount epsilon) input.q_positive
  second := sourceResponseUniverse input.q (n + 1) (quantileCount epsilon) input.q_positive (by omega)
  scaleA := input.scaleA
  scaleB := input.scaleB
  scaleA_nonnegative := input.scaleA_nonnegative
  scaleB_nonnegative := input.scaleB_nonnegative
  budgetA := input.budgetA
  budgetB := input.budgetB
  budgetA_nonnegative := input.budgetA_positive.le
  budgetB_nonnegative := input.budgetB_positive.le
  values := input.values
  eta := 1/8
  theta := 1/8
  eta_unit := by norm_num
  theta_unit := by norm_num

def Input.directInput {n : ℕ} (input : Input (n + 1)) (epsilon : ℚ) (he : 0 < epsilon ∧ epsilon ≤ 1) :
    FareyImplicitTrainer.DirectInput (n + 1) := (input.directBase epsilon).withAccuracy epsilon he

theorem directBase_trainer {n : ℕ} (input : Input (n + 1)) (epsilon : ℚ) :
    (input.directBase epsilon).trainer = input.base epsilon := rfl

theorem directBase_config {n : ℕ} (input : Input (n + 1)) (epsilon : ℚ) :
    (input.directBase epsilon).config = input.baseConfig epsilon := rfl

theorem directInput_trainer {n : ℕ} (input : Input (n + 1)) (epsilon : ℚ) (he : 0 < epsilon ∧ epsilon ≤ 1) :
    (input.directInput epsilon he).trainer = input.trainer epsilon he := rfl

theorem directInput_config {n : ℕ} (input : Input (n + 1)) (epsilon : ℚ) (he : 0 < epsilon ∧ epsilon ≤ 1) :
    (input.directInput epsilon he).config = input.config epsilon he := rfl

def Input.directPreparedA {n : ℕ} (input : Input (n + 1)) (epsilon : ℚ) (he : 0 < epsilon ∧ epsilon ≤ 1)
    (history : List (RawObservation (n + 1))) : ExactSizedDraw (n + 1) := (input.directInput epsilon he).preparedA history

def Input.directPreparedB {n : ℕ} (input : Input (n + 1)) (epsilon : ℚ) (he : 0 < epsilon ∧ epsilon ≤ 1)
    (history : List (RawObservation (n + 1))) : ExactSizedDraw (n + 1) := (input.directInput epsilon he).preparedB history

theorem directPreparedA_model {n : ℕ} (input : Input (n + 1)) (epsilon : ℚ) (he : 0 < epsilon ∧ epsilon ≤ 1)
    (history : List (RawObservation (n + 1))) :
    (input.directPreparedA epsilon he history).model = (input.trainer epsilon he).compactPreparedA (input.config epsilon he) history :=
  (input.directInput epsilon he).preparedA_model history

theorem directPreparedB_model {n : ℕ} (input : Input (n + 1)) (epsilon : ℚ) (he : 0 < epsilon ∧ epsilon ≤ 1)
    (history : List (RawObservation (n + 1))) :
    (input.directPreparedB epsilon he history).model = (input.trainer epsilon he).compactPreparedB (input.config epsilon he) history :=
  (input.directInput epsilon he).preparedB_model history

def Input.directNativeRun {n : ℕ} (input : Input (n + 1)) (epsilon : ℚ) (he : 0 < epsilon ∧ epsilon ≤ 1)
    (epsilonA epsilonB : ℚ) (K B T : ℕ) (bits : Fin (T * B) → Bool) : List (RawObservation (n + 1)) :=
  ExactPreparedTrainingHistory.run (input.directPreparedA epsilon he) (input.directPreparedB epsilon he) input.values
    epsilonA epsilonB K B T bits []

theorem directNativeRun_refines {n : ℕ} (input : Input (n + 1)) (epsilon : ℚ) (he : 0 < epsilon ∧ epsilon ≤ 1)
    (epsilonA epsilonB : ℚ) (K B T : ℕ) (bits : Fin (T * B) → Bool) :
    input.directNativeRun epsilon he epsilonA epsilonB K B T bits =
      (input.trainer epsilon he).compactNativeRun (input.config epsilon he) epsilonA epsilonB K B T bits := by
  unfold Input.directNativeRun
  rw [ExactPreparedTrainingHistory.run_refines]
  have hA : (fun history => (input.directPreparedA epsilon he history).model) =
      (input.trainer epsilon he).compactPreparedA (input.config epsilon he) := by
    funext history
    exact directPreparedA_model input epsilon he history
  have hB : (fun history => (input.directPreparedB epsilon he history).model) =
      (input.trainer epsilon he).compactPreparedB (input.config epsilon he) := by
    funext history
    exact directPreparedB_model input epsilon he history
  rw [hA,hB]
  rfl

theorem directPrepared_horizon_cap {n : ℕ} (input : Input (n + 1)) (epsilon : ℚ) (he : 0 < epsilon ∧ epsilon ≤ 1)
    (accuracy : ℚ) (ha : 0 < accuracy) : ∀ history : List (RawObservation (n + 1)), history.length < input.rounds epsilon →
    ExactSizedTrainingTransition.bitBudget (input.directPreparedA epsilon he history) (input.directPreparedB epsilon he history) input.values
      (adaptiveDrawTolerance accuracy (input.rounds epsilon)) (adaptiveDrawTolerance accuracy (input.rounds epsilon))
      (adaptiveFieldPrecision accuracy (input.rounds epsilon)) ≤ input.seedCap epsilon he accuracy := by
  intro history hLength
  unfold ExactSizedTrainingTransition.bitBudget ExactSizedDraw.bitBudget
  rw [directPreparedA_model,directPreparedB_model]
  exact (input.trainer epsilon he).compactHorizon_seedCap (input.config epsilon he) (input.rounds epsilon)
    (input.width epsilon) (input.width epsilon) (source_widths input epsilon).1 (source_widths input epsilon).2
    accuracy ha history hLength

def Input.directRun {n : ℕ} (input : Input (n + 1)) (epsilon : ℚ) (he : 0 < epsilon ∧ epsilon ≤ 1) (accuracy : ℚ)
    (bits : Fin (input.rounds epsilon * input.seedCap epsilon he accuracy) → Bool) : List (RawObservation (n + 1)) :=
  input.directNativeRun epsilon he (adaptiveDrawTolerance accuracy (input.rounds epsilon))
    (adaptiveDrawTolerance accuracy (input.rounds epsilon)) (adaptiveFieldPrecision accuracy (input.rounds epsilon))
    (input.seedCap epsilon he accuracy) (input.rounds epsilon) bits

theorem directRun_refines {n : ℕ} (input : Input (n + 1)) (epsilon : ℚ) (he : 0 < epsilon ∧ epsilon ≤ 1)
    (accuracy : ℚ) (bits : Fin (input.rounds epsilon * input.seedCap epsilon he accuracy) → Bool) :
    input.directRun epsilon he accuracy bits = input.run epsilon he accuracy bits :=
  directNativeRun_refines input epsilon he _ _ _ _ _ bits

theorem directRun_feasible {n : ℕ} (input : Input (n + 1)) (epsilon : ℚ) (he : 0 < epsilon ∧ epsilon ≤ 1)
    (accuracy : ℚ) (ha : 0 < accuracy) (bits : Fin (input.rounds epsilon * input.seedCap epsilon he accuracy) → Bool) :
    ∀ observation ∈ input.directRun epsilon he accuracy bits,
      Feasible (input.budgetA : ℝ) (fun field => (observation.1 field : ℝ)) ∧
        Feasible (input.budgetB : ℝ) (fun field => (observation.2.1 field : ℝ)) := by
  rw [directRun_refines]
  exact run_feasible input epsilon he accuracy ha bits

theorem directRun_error {n : ℕ} (input : Input (n + 1)) (epsilon : ℚ) (he : 0 < epsilon ∧ epsilon ≤ 1)
    (accuracy : ℚ) (ha : 0 < accuracy) (test : List (RawObservation (n + 1)) → ℝ)
    (hTest : ∀ history, 0 ≤ test history ∧ test history ≤ 1) :
    |(fairBitKernel (input.rounds epsilon * input.seedCap epsilon he accuracy)).mean
        (fun bits => test (input.directRun epsilon he accuracy bits)) -
      SparseMW.historyMean (input.trainer epsilon he).transition (input.rounds epsilon)
        (fun history => test (history.map (input.trainer epsilon he).encodeObservation))| ≤ (accuracy : ℝ) := by
  simp_rw [directRun_refines]
  exact run_error input epsilon he accuracy ha test hTest

theorem directRun_bad_gap_bound {n : ℕ} (input : Input (n + 1)) (epsilon : ℚ) (he : 0 < epsilon ∧ epsilon ≤ 1)
    (accuracy : ℚ) (ha : 0 < accuracy) :
    (fairBitKernel (input.rounds epsilon * input.seedCap epsilon he accuracy)).mean (fun bits =>
      if (epsilon : ℝ) / 8 < (input.trainer epsilon he).rawGap (input.directRun epsilon he accuracy bits) then 1 else 0) ≤
        1 / 16 + (accuracy : ℝ) := by
  simp_rw [directRun_refines]
  exact run_bad_gap_bound input epsilon he accuracy ha

end Blotto.FareySourceTraining
