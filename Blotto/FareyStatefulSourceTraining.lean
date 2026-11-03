import Blotto.FareyStatefulTraining
import Blotto.FareyDirectSourceTraining

/-! Source-derived finite security training now carries actual block state.
Every seed yields exactly the original source history; its computed seed cap,
finite confidence and hard budgets transfer without a simulation premise.
Original-game compilation, continuous output and full computation prices are
not certified by this stateful execution equality. -/

namespace Blotto.FareySourceTraining
open FareyImplicitTrainer ImplicitLeafCounts ProductSecurityTrainer
open scoped BigOperators

def Input.statefulNativeResult {n : ℕ} (input : Input (n + 1)) (epsilon : ℚ) (he : 0 < epsilon ∧ epsilon ≤ 1)
    (epsilonA epsilonB : ℚ) (K B T : ℕ) (bits : Fin (T * B) → Bool) :
    NativeBlockState (input.directInput epsilon he) × List (RawObservation (n + 1)) :=
  NativeBlockState.run (input.directInput epsilon he) epsilonA epsilonB K B T bits

theorem statefulNative_refines {n : ℕ} (input : Input (n + 1)) (epsilon : ℚ) (he : 0 < epsilon ∧ epsilon ≤ 1)
    (epsilonA epsilonB : ℚ) (K B T : ℕ) (bits : Fin (T * B) → Bool) :
    (input.statefulNativeResult epsilon he epsilonA epsilonB K B T bits).2 =
      input.directNativeRun epsilon he epsilonA epsilonB K B T bits :=
  NativeBlockState.run_refines (input.directInput epsilon he) epsilonA epsilonB K B T bits

theorem statefulNative_matches {n : ℕ} (input : Input (n + 1)) (epsilon : ℚ) (he : 0 < epsilon ∧ epsilon ≤ 1)
    (epsilonA epsilonB : ℚ) (K B T : ℕ) (bits : Fin (T * B) → Bool) :
    (input.statefulNativeResult epsilon he epsilonA epsilonB K B T bits).1.Matches
      (input.statefulNativeResult epsilon he epsilonA epsilonB K B T bits).2 :=
  NativeBlockState.run_matches (input.directInput epsilon he) epsilonA epsilonB K B T bits

theorem statefulNative_length {n : ℕ} (input : Input (n + 1)) (epsilon : ℚ) (he : 0 < epsilon ∧ epsilon ≤ 1)
    (epsilonA epsilonB : ℚ) (K B T : ℕ) (bits : Fin (T * B) → Bool) :
    (input.statefulNativeResult epsilon he epsilonA epsilonB K B T bits).2.length = T := by
  rw [statefulNative_refines]
  unfold Input.directNativeRun ExactPreparedTrainingHistory.run
  simpa only [List.length_nil,Nat.add_zero] using runBitHistory_length B _ T bits []

def Input.statefulResult {n : ℕ} (input : Input (n + 1)) (epsilon : ℚ) (he : 0 < epsilon ∧ epsilon ≤ 1) (accuracy : ℚ)
    (bits : Fin (input.rounds epsilon * input.seedCap epsilon he accuracy) → Bool) :
    NativeBlockState (input.directInput epsilon he) × List (RawObservation (n + 1)) :=
  input.statefulNativeResult epsilon he (adaptiveDrawTolerance accuracy (input.rounds epsilon))
    (adaptiveDrawTolerance accuracy (input.rounds epsilon)) (adaptiveFieldPrecision accuracy (input.rounds epsilon))
    (input.seedCap epsilon he accuracy) (input.rounds epsilon) bits

def Input.statefulRun {n : ℕ} (input : Input (n + 1)) (epsilon : ℚ) (he : 0 < epsilon ∧ epsilon ≤ 1) (accuracy : ℚ)
    (bits : Fin (input.rounds epsilon * input.seedCap epsilon he accuracy) → Bool) : List (RawObservation (n + 1)) :=
  (input.statefulResult epsilon he accuracy bits).2

theorem statefulRun_refines {n : ℕ} (input : Input (n + 1)) (epsilon : ℚ) (he : 0 < epsilon ∧ epsilon ≤ 1)
    (accuracy : ℚ) (bits : Fin (input.rounds epsilon * input.seedCap epsilon he accuracy) → Bool) :
    input.statefulRun epsilon he accuracy bits = input.run epsilon he accuracy bits :=
  (statefulNative_refines input epsilon he _ _ _ _ _ bits).trans (directRun_refines input epsilon he accuracy bits)

theorem statefulResult_matches {n : ℕ} (input : Input (n + 1)) (epsilon : ℚ) (he : 0 < epsilon ∧ epsilon ≤ 1)
    (accuracy : ℚ) (bits : Fin (input.rounds epsilon * input.seedCap epsilon he accuracy) → Bool) :
    (input.statefulResult epsilon he accuracy bits).1.Matches (input.statefulRun epsilon he accuracy bits) :=
  statefulNative_matches input epsilon he _ _ _ _ _ bits

theorem statefulRun_length {n : ℕ} (input : Input (n + 1)) (epsilon : ℚ) (he : 0 < epsilon ∧ epsilon ≤ 1)
    (accuracy : ℚ) (bits : Fin (input.rounds epsilon * input.seedCap epsilon he accuracy) → Bool) :
    (input.statefulRun epsilon he accuracy bits).length = input.rounds epsilon :=
  statefulNative_length input epsilon he _ _ _ _ _ bits

theorem statefulRun_feasible {n : ℕ} (input : Input (n + 1)) (epsilon : ℚ) (he : 0 < epsilon ∧ epsilon ≤ 1)
    (accuracy : ℚ) (ha : 0 < accuracy) (bits : Fin (input.rounds epsilon * input.seedCap epsilon he accuracy) → Bool) :
    ∀ observation ∈ input.statefulRun epsilon he accuracy bits,
      Feasible (input.budgetA : ℝ) (fun field => (observation.1 field : ℝ)) ∧
        Feasible (input.budgetB : ℝ) (fun field => (observation.2.1 field : ℝ)) := by
  rw [statefulRun_refines]
  exact run_feasible input epsilon he accuracy ha bits

theorem statefulRun_error {n : ℕ} (input : Input (n + 1)) (epsilon : ℚ) (he : 0 < epsilon ∧ epsilon ≤ 1)
    (accuracy : ℚ) (ha : 0 < accuracy) (test : List (RawObservation (n + 1)) → ℝ)
    (hTest : ∀ history, 0 ≤ test history ∧ test history ≤ 1) :
    |(fairBitKernel (input.rounds epsilon * input.seedCap epsilon he accuracy)).mean
        (fun bits => test (input.statefulRun epsilon he accuracy bits)) -
      SparseMW.historyMean (input.trainer epsilon he).transition (input.rounds epsilon)
        (fun history => test (history.map (input.trainer epsilon he).encodeObservation))| ≤ (accuracy : ℝ) := by
  simp_rw [statefulRun_refines]
  exact run_error input epsilon he accuracy ha test hTest

theorem statefulRun_bad_gap_bound {n : ℕ} (input : Input (n + 1)) (epsilon : ℚ) (he : 0 < epsilon ∧ epsilon ≤ 1)
    (accuracy : ℚ) (ha : 0 < accuracy) :
    (fairBitKernel (input.rounds epsilon * input.seedCap epsilon he accuracy)).mean (fun bits =>
      if (epsilon : ℝ) / 8 < (input.trainer epsilon he).rawGap (input.statefulRun epsilon he accuracy bits) then 1 else 0) ≤
        1 / 16 + (accuracy : ℝ) := by
  simp_rw [statefulRun_refines]
  exact run_bad_gap_bound input epsilon he accuracy ha

theorem statefulResult_first_blocks {n : ℕ} (input : Input (n + 1)) (epsilon : ℚ) (he : 0 < epsilon ∧ epsilon ≤ 1)
    (accuracy : ℚ) (bits : Fin (input.rounds epsilon * input.seedCap epsilon he accuracy) → Bool) :
    (∑ field, ((input.statefulResult epsilon he accuracy bits).1.first.read field).length) ≤ n + 1 + 2 * input.rounds epsilon := by
  have h := (input.statefulResult epsilon he accuracy bits).1.first_total_blocks
    (input.statefulRun epsilon he accuracy bits) (statefulResult_matches input epsilon he accuracy bits)
  rwa [statefulRun_length] at h

theorem statefulResult_second_blocks {n : ℕ} (input : Input (n + 1)) (epsilon : ℚ) (he : 0 < epsilon ∧ epsilon ≤ 1)
    (accuracy : ℚ) (bits : Fin (input.rounds epsilon * input.seedCap epsilon he accuracy) → Bool) :
    (∑ field, ((input.statefulResult epsilon he accuracy bits).1.second.read field).length) ≤ n + 1 + 2 * input.rounds epsilon := by
  have h := (input.statefulResult epsilon he accuracy bits).1.second_total_blocks
    (input.statefulRun epsilon he accuracy bits) (statefulResult_matches input epsilon he accuracy bits)
  rwa [statefulRun_length] at h

end Blotto.FareySourceTraining
