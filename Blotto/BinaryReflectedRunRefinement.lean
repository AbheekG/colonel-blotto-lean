import Blotto.BinaryReflectedSerialValue
import Blotto.WordMappedIndexedRefinement

/-! The actual source-free Boolean reflected run has exactly the retained
whole source serial output and final shared-reader position, including none. -/

namespace Blotto.BinaryReflectedRunRefinement
open BinaryRationalNormalization BinaryRationalEncoding BinaryReflectedFourSetup
open BinarySharedResourceRun BinaryReflectedSerialRun BinaryReflectedPhaseRefinement BinaryReflectedSerialValue

noncomputable def sourceRunResult (source : RationalFourInput)
    (hCase : source.w < (1-source.p)*source.ell) (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) :
    Option (Fin 4 → ℚ) × ℕ :=
  let system := source.reflectedResourceSystem hCase
  let result := (system.machine K outer scalar).run N system.samplingStart bits
  (result.1.map (RationalAffineAllocation.reflectAppend source.originalLengths).value,result.2)

theorem run_refines (input : BinaryFourParameters.Input) (source : RationalFourInput) (hC : input.Canonical)
    (hr : input.Refines source) (hCase : source.w < (1-source.p)*source.ell) (hAd : Admissible input)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) :
    ((run input hC hAd K N outer scalar bits).1.map sourceRow,(run input hC hAd K N outer scalar bits).2) =
      sourceRunResult source hCase K N outer scalar bits := by
  unfold sourceRunResult
  dsimp only
  rw [RationalNestedResourceSystem.machine_run_serial]
  cases hResult : (setupRun input hC N bits).1 with
  | none =>
    have hNone := (setupRun_phase_failure_iff input source hC hr hCase N bits).mp hResult
    have hPos := setupRun_phase_position input source hC hr hCase N bits
    unfold BinaryReflectedSerialRun.run
    rw [BinaryReflectedSerialSelection.select_resource_failure input hC hAd K N outer bits hResult]
    simp only [hNone,WordStateMachine.handoff,Option.map_none]
    exact Prod.ext rfl hPos
  | some result =>
    let phase := phaseResult input source hC hr hCase N bits result hResult
    have hPhase := setupRun_phase_success input source hC hr hCase N bits result hResult
    have hPos := setupRun_phase_position input source hC hr hCase N bits
    have hFit := (source.reflectedResourceSystem hCase).phase.run_bits_le N (source.reflectedResourceSystem hCase).start bits
    unfold BinaryReflectedSerialRun.run
    rw [BinaryReflectedSerialSelection.selected_categorical_refines input source hC hr hCase hAd K N outer bits result hResult]
    simp only [hPhase,WordStateMachine.handoff,hFit,dite_true]
    simp only [← hPos]
    unfold RationalNestedResourceSystem.continuationMachine RationalNestedResourceSystem.continuationStart RationalSegmentLottery.machine
    rw [WordMappedIndexedRefinement.indexed_refines]
    simp only [WordMappedIndexedRefinement.mapResult,Option.map_map,Function.comp_def]
    apply Prod.ext
    · apply congrArg (fun f =>
        (((categoricalMachine (0 : Fin 18)).runCursorIndexed N bits
          (.state (((source.reflectedResourceSystem hCase).terminalData phase).profile K outer).start)
          (setupRun input hC N bits).2 (setupRun_position input hC N bits)).1.map f))
      funext slot j
      exact emission_value input source hC hr hCase N bits result hResult K outer scalar slot j
    · rfl

end Blotto.BinaryReflectedRunRefinement
