import Blotto.RealWordExecutionLaw
import Blotto.RealStateMachineCounts
import Blotto.RationalLottoResourceSystem

/-! The actual native general resource phase can be driven by exact real
uniform comparisons. Its selected updates, terminal certificates, means and
linear number of requests are the existing source controller's ones. This
does not yet compile the continuous local terminal couplers. -/

namespace Blotto.RationalLottoResourceSystem

noncomputable def realPhaseFallback {n : ℕ} (i : RationalLottoResourceSystem n) : i.PhaseResult :=
  i.phase.chooseLeaf i.start

noncomputable def realPhaseSample {n : ℕ} (i : RationalLottoResourceSystem n) (seed : Fin (n - 1) → ℝ) : i.PhaseResult :=
  i.phase.realMachine.output (n - 1) i.start i.realPhaseFallback seed

theorem realPhase_total {n : ℕ} (i : RationalLottoResourceSystem n) (seed : Fin (n - 1) → ℝ) :
    (i.phase.realMachine.run (n - 1) i.start seed).1 ≠ none :=
  i.phase.realMachine.run_total (n - 1) i.start seed i.phase_rank

theorem realPhase_resource_contract {n : ℕ} (i : RationalLottoResourceSystem n) (seed : Fin (n - 1) → ℝ) :
    RationalResourceInvariant i.length (2 * (i.B : ℝ)) (i.realPhaseSample seed).1 ∧
      (i.realPhaseSample seed).1.active.length ≤ 1 := (i.realPhaseSample seed).2

theorem realPhase_reads {n : ℕ} (i : RationalLottoResourceSystem n) (seed : Fin (n - 1) → ℝ) :
    (i.phase.realMachine.run (n - 1) i.start seed).2 ≤ n - 1 :=
  (i.phase.realMachine.run_reads_rank (n - 1) i.start seed).trans i.phase_rank

theorem realPhase_calls {n : ℕ} (i : RationalLottoResourceSystem n) (seed : Fin (n - 1) → ℝ) :
    i.phase.realMachine.visits (n - 1) seed i.start 0 (Nat.zero_le _) ≤ (n - 1) + 1 :=
  (i.phase.realMachine.visits_bound (n - 1) seed i.start 0 (Nat.zero_le _)).trans (Nat.add_le_add_right i.phase_rank 1)

theorem realPhase_coordinate_mean {n : ℕ} (i : RationalLottoResourceSystem n) (j : Fin n) :
    (i.phase.realMachine.specification i.start).mean (fun s => ((i.terminalData s).resource j : ℝ)) = (i.initial j : ℝ) := by
  rw [i.phase.realMachine_specification, WordChoiceTree.realChoice_mean]
  exact i.phase_mean j

end Blotto.RationalLottoResourceSystem
