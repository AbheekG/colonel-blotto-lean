import Blotto.FareyStoredObservation
import Blotto.ExactPreparedTrainingHistory

/-! The native trainer carries current block arrays and updates only the
observed field. Per-round preparation reads those arrays once per player.
History is retained for the required output, but is not replayed for weights.
The exact history invariant derives every-seed simulation; runtime/physical
array ownership and complete guide/decoder costs remain separate. -/

namespace Blotto.FareyImplicitTrainer
open ImplicitLeafCounts ProductSecurityTrainer
namespace NativeBlockState

def sample {n : ℕ} {input : DirectInput (n + 1)} (state : NativeBlockState input)
    (epsilonA epsilonB : ℚ) (K B : ℕ) (bits : Fin B → Bool) : RawObservation (n + 1) :=
  (state.storedSample epsilonA epsilonB K B bits).reference

theorem sample_refines {n : ℕ} {input : DirectInput (n + 1)} (state : NativeBlockState input)
    (history : List (RawObservation (n + 1))) (h : state.Matches history)
    (epsilonA epsilonB : ℚ) (K B : ℕ) (bits : Fin B → Bool) :
    state.sample epsilonA epsilonB K B bits =
      ExactPreparedTrainingHistory.sample input.preparedA input.preparedB input.values epsilonA epsilonB K B history bits :=
  (state.storedSample_reference epsilonA epsilonB K B bits).trans
    (congrArg₂ (fun first second => ExactPreparedTrainingHistory.preparedSample first second input.values epsilonA epsilonB K B bits)
      (state.preparedA_eq_history history h) (state.preparedB_eq_history history h))

def runFrom {n : ℕ} {input : DirectInput (n + 1)} (epsilonA epsilonB : ℚ) (K B : ℕ) :
    (T : ℕ) → (Fin (T * B) → Bool) → NativeBlockState input → List (RawObservation (n + 1)) →
      NativeBlockState input × List (RawObservation (n + 1))
  | 0, _, state, history => (state,history)
  | T + 1, bits, state, history =>
      let flat : Fin (B + T * B) → Bool := fun j => bits (j.cast (by ring))
      let observed := state.sample epsilonA epsilonB K B (firstBitBlock B (T * B) flat)
      let next := state.step observed
      runFrom epsilonA epsilonB K B T (secondBitBlock B (T * B) flat) next (observed :: history)

theorem runFrom_refines {n : ℕ} {input : DirectInput (n + 1)} (epsilonA epsilonB : ℚ) (K B T : ℕ)
    (bits : Fin (T * B) → Bool) (state : NativeBlockState input) (history : List (RawObservation (n + 1)))
    (h : state.Matches history) :
    (runFrom epsilonA epsilonB K B T bits state history).1.Matches (runFrom epsilonA epsilonB K B T bits state history).2 ∧
      (runFrom epsilonA epsilonB K B T bits state history).2 =
        ExactPreparedTrainingHistory.run input.preparedA input.preparedB input.values epsilonA epsilonB K B T bits history := by
  induction T generalizing state history with
  | zero => exact ⟨h,rfl⟩
  | succ T ih =>
      let flat : Fin (B + T * B) → Bool := fun j => bits (j.cast (by ring))
      let observed := state.sample epsilonA epsilonB K B (firstBitBlock B (T * B) flat)
      have hn := state.step_matches history h observed
      have he := ih (secondBitBlock B (T * B) flat) (state.step observed) (observed :: history) hn
      refine ⟨he.1,he.2.trans ?_⟩
      unfold ExactPreparedTrainingHistory.run
      conv_rhs => rw [runBitHistory]
      rw [←sample_refines state history h]

def run {n : ℕ} (input : DirectInput (n + 1)) (epsilonA epsilonB : ℚ) (K B T : ℕ)
    (bits : Fin (T * B) → Bool) : NativeBlockState input × List (RawObservation (n + 1)) :=
  runFrom epsilonA epsilonB K B T bits (initial input) []

theorem run_matches {n : ℕ} (input : DirectInput (n + 1)) (epsilonA epsilonB : ℚ) (K B T : ℕ)
    (bits : Fin (T * B) → Bool) : (run input epsilonA epsilonB K B T bits).1.Matches (run input epsilonA epsilonB K B T bits).2 :=
  (runFrom_refines epsilonA epsilonB K B T bits (initial input) [] (initial_matches input)).1

theorem run_refines {n : ℕ} (input : DirectInput (n + 1)) (epsilonA epsilonB : ℚ) (K B T : ℕ)
    (bits : Fin (T * B) → Bool) :
    (run input epsilonA epsilonB K B T bits).2 =
      ExactPreparedTrainingHistory.run input.preparedA input.preparedB input.values epsilonA epsilonB K B T bits [] :=
  (runFrom_refines epsilonA epsilonB K B T bits (initial input) [] (initial_matches input)).2

theorem run_feasible {n : ℕ} (input : DirectInput (n + 1)) (epsilonA epsilonB : ℚ) (hA : 0 < epsilonA) (hB : 0 < epsilonB)
    (K B T : ℕ) (bits : Fin (T * B) → Bool) :
    ∀ observation ∈ (run input epsilonA epsilonB K B T bits).2,
      Feasible (input.budgetA : ℝ) (fun field => (observation.1 field : ℝ)) ∧
        Feasible (input.budgetB : ℝ) (fun field => (observation.2.1 field : ℝ)) := by
  rw [run_refines]
  exact ExactPreparedTrainingHistory.run_feasible input.preparedA input.preparedB input.values epsilonA epsilonB hA hB K B
    input.budgetA input.budgetB input.preparedA_budget input.preparedB_budget T bits [] (by simp)

end NativeBlockState
end Blotto.FareyImplicitTrainer
