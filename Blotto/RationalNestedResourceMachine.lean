import Blotto.RationalNestedResourceLaw
import Blotto.RationalSegmentMachine
import Blotto.WordMachineFallback

/-! Native serial sampling of a three-resource phase and its terminal
segment table. All coin requests share one caller-supplied cap. Outer/scalar
blocks are fixed inputs to the controller and remain fresh fair draws. -/

namespace Blotto.RationalNestedResourceSystem

abbrev PhaseCursor (i : RationalNestedResourceSystem) :=
  {cursor : RationalResourceCursor i.capacity // i.CursorInvariant cursor}
abbrev PhaseResult (i : RationalNestedResourceSystem) :=
  {s : RationalActiveResources i.capacity // i.TerminalState s}
abbrev SamplingState (i : RationalNestedResourceSystem) := SerialState i.PhaseCursor i.PhaseResult (fun _ => CategoricalState (Fin 18))

def continuationMachine (i : RationalNestedResourceSystem) (K : ℕ) (outerBits scalarBits : Fin K → Bool)
    (s : i.PhaseResult) : WordStateMachine (CategoricalState (Fin 18)) (Fin 3 → ℚ) :=
  ((i.terminalData s).profile K outerBits).machine 0 K scalarBits

def continuationStart (i : RationalNestedResourceSystem) (K : ℕ) (outerBits : Fin K → Bool)
    (s : i.PhaseResult) : CategoricalState (Fin 18) := ((i.terminalData s).profile K outerBits).start

theorem continuation_rank (i : RationalNestedResourceSystem) (K : ℕ) (outerBits scalarBits : Fin K → Bool)
    (s : i.PhaseResult) : (i.continuationMachine K outerBits scalarBits s).rank (i.continuationStart K outerBits s) ≤ 17 := by
  exact le_of_eq (((i.terminalData s).profile K outerBits).machine_rank 0 K scalarBits)

def machine (i : RationalNestedResourceSystem) (K : ℕ) (outerBits scalarBits : Fin K → Bool) :
    WordStateMachine i.SamplingState (Fin 3 → ℚ) :=
  i.phase.serial (i.continuationMachine K outerBits scalarBits) (i.continuationStart K outerBits) 17
    (i.continuation_rank K outerBits scalarBits)

def samplingStart (i : RationalNestedResourceSystem) : i.SamplingState := .source i.start

theorem machine_rank (i : RationalNestedResourceSystem) (K : ℕ) (outerBits scalarBits : Fin K → Bool) :
    (i.machine K outerBits scalarBits).rank i.samplingStart ≤ 19 := by
  change i.phase.rank i.start + 17 ≤ 19
  have h := i.phase_rank
  omega

def PathContract (i : RationalNestedResourceSystem) (x : Fin 3 → ℚ) : Prop :=
  FullBudget (i.M : ℝ) (fun j => (x j : ℝ)) ∧ InBox (fun j => (i.long j : ℝ)) (fun j => (x j : ℝ))

theorem machine_forLeaves (i : RationalNestedResourceSystem) (K : ℕ) (outerBits scalarBits : Fin K → Bool) :
    ((i.machine K outerBits scalarBits).specification i.samplingStart).decode.ForLeaves i.PathContract := by
  rw [machine, samplingStart, WordStateMachine.serial_source_specification]
  apply WordChoiceTree.bind_forLeaves
  intro s
  apply RationalSegmentLottery.machine_forLeaves
  intro slot
  exact ⟨((i.terminalData s).profile K outerBits).point_fullBudget K ((i.terminalData s).profile_endpoints K outerBits) slot scalarBits,
    ((i.terminalData s).profile K outerBits).point_inBox K _ ((i.terminalData s).profile_box K outerBits) slot scalarBits⟩

def fallback (i : RationalNestedResourceSystem) (K : ℕ) (outerBits scalarBits : Fin K → Bool) : Fin 3 → ℚ :=
  (i.machine K outerBits scalarBits).chooseLeaf i.samplingStart

theorem fallback_contract (i : RationalNestedResourceSystem) (K : ℕ) (outerBits scalarBits : Fin K → Bool) :
    i.PathContract (i.fallback K outerBits scalarBits) :=
  (i.machine K outerBits scalarBits).chooseLeaf_forLeaves i.samplingStart _ (i.machine_forLeaves K outerBits scalarBits)

def fixedSample (i : RationalNestedResourceSystem) (K R : ℕ) (outerBits scalarBits : Fin K → Bool)
    (choiceBits : Fin R → Bool) : Fin 3 → ℚ :=
  (i.machine K outerBits scalarBits).output R i.samplingStart (i.fallback K outerBits scalarBits) choiceBits

theorem fixedSample_contract (i : RationalNestedResourceSystem) (K R : ℕ) (outerBits scalarBits : Fin K → Bool)
    (choiceBits : Fin R → Bool) : i.PathContract (i.fixedSample K R outerBits scalarBits choiceBits) := by
  rw [fixedSample, WordStateMachine.output_refines]
  exact WordChoiceTree.output_forLeaves _ _ _ _ _ (i.machine_forLeaves K outerBits scalarBits) (i.fallback_contract K outerBits scalarBits)

theorem machine_mean (i : RationalNestedResourceSystem) (K : ℕ) (outerBits scalarBits : Fin K → Bool)
    (f : (Fin 3 → ℚ) → ℝ) :
    ((i.machine K outerBits scalarBits).specification i.samplingStart).decode.mean f =
      (i.phase.specification i.start).decode.mean (fun s =>
        ∑ slot, (((i.terminalData s).profile K outerBits).weight slot : ℝ) *
          f (((i.terminalData s).profile K outerBits).point K slot scalarBits)) := by
  rw [machine, samplingStart, WordStateMachine.serial_mean]
  congr 1
  funext s
  exact ((i.terminalData s).profile K outerBits).machine_mean 0 K scalarBits f

end Blotto.RationalNestedResourceSystem
