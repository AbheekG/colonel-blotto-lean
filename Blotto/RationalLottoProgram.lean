import Blotto.RationalLottoResourceSystem
import Blotto.RationalTerminalProgram

/-! One native controller joins general resource rounding and its selected
terminal coupling under the same coin cap. Budget holds on every returned
path; global midpoint/CDF/Nash and computational costs are separate proofs. -/

namespace Blotto.RationalLottoResourceSystem

abbrev SamplingState {n : ℕ} (i : RationalLottoResourceSystem n) (K : ℕ) (outerBits scalarBits : Fin K → Bool) :=
  SerialState i.PhaseCursor i.PhaseResult (fun s => ((i.terminalData s).program K outerBits scalarBits).State)

def machine {n : ℕ} (i : RationalLottoResourceSystem n) (K : ℕ) (outerBits scalarBits : Fin K → Bool) :
    WordStateMachine (i.SamplingState K outerBits scalarBits) (Fin n → ℚ) :=
  i.phase.serial (fun s => ((i.terminalData s).program K outerBits scalarBits).machine)
    (fun s => ((i.terminalData s).program K outerBits scalarBits).start) 80
    (fun s => ((i.terminalData s).program K outerBits scalarBits).rank_le)

def samplingStart {n : ℕ} (i : RationalLottoResourceSystem n) (K : ℕ) (outerBits scalarBits : Fin K → Bool) :
    i.SamplingState K outerBits scalarBits := .source i.start

def program {n : ℕ} (i : RationalLottoResourceSystem n) (K : ℕ) (outerBits scalarBits : Fin K → Bool) :
    RationalAllocationProgram n (n - 1 + 80) where
  State := i.SamplingState K outerBits scalarBits
  machine := i.machine K outerBits scalarBits
  start := i.samplingStart K outerBits scalarBits
  rank_le := by
    change i.phase.rank i.start + 80 ≤ n - 1 + 80
    exact Nat.add_le_add_right i.phase_rank 80

theorem program_leavesBudget {n : ℕ} (i : RationalLottoResourceSystem n) (K : ℕ)
    (outerBits scalarBits : Fin K → Bool) : (i.program K outerBits scalarBits).LeavesBudget i.B := by
  change ((i.machine K outerBits scalarBits).specification (i.samplingStart K outerBits scalarBits)).decode.ForLeaves _
  rw [machine, samplingStart, WordStateMachine.serial_source_specification]
  apply WordChoiceTree.bind_forLeaves
  exact fun s => (i.terminalData s).program_leavesBudget K outerBits scalarBits

theorem program_rank_paper_bound {n : ℕ} (i : RationalLottoResourceSystem n) (K : ℕ)
    (outerBits scalarBits : Fin K → Bool) :
    (i.program K outerBits scalarBits).machine.rank (i.program K outerBits scalarBits).start ≤ n + 1000 := by
  have h := (i.program K outerBits scalarBits).rank_le
  omega

theorem program_sample_fullBudget {n : ℕ} (i : RationalLottoResourceSystem n) (K R : ℕ)
    (outerBits scalarBits : Fin K → Bool) (choiceBits : Fin R → Bool) :
    FullBudget (i.B : ℝ) (fun j => ((i.program K outerBits scalarBits).sample R choiceBits j : ℝ)) :=
  (i.program K outerBits scalarBits).sample_fullBudget (i.program_leavesBudget K outerBits scalarBits) R choiceBits

theorem program_cap_CDF_error {n : ℕ} (i : RationalLottoResourceSystem n) (K : ℕ)
    (outerBits scalarBits : Fin K → Bool) :
    CDFClose ((i.program K outerBits scalarBits).sampleLaw (3 * (n + 1000 + K)))
      (i.program K outerBits scalarBits).idealLaw (1 / (2 : ℝ) ^ K) :=
  (i.machine K outerBits scalarBits).rationalCappedLaw_CDF_error (n + 1000) K
    (i.samplingStart K outerBits scalarBits) (i.program_rank_paper_bound K outerBits scalarBits)
    (i.program K outerBits scalarBits).fallback

end Blotto.RationalLottoResourceSystem
