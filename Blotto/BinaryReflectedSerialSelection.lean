import Blotto.BinaryReflectedSerialRun
import Blotto.BinaryReflectedPhaseRefinement

/-! Native terminal slot selection is exactly the retained phase result followed
by categorical execution at its returned position, in the same global reader.
Mappings here are proof views; the native entry point accepts no source data. -/

namespace Blotto.BinaryReflectedSerialSelection
open BinaryRationalNormalization BinaryRationalEncoding BinaryReflectedFourSetup
open BinarySharedResourceRun BinaryReflectedSerialRun BinaryReflectedPhaseRefinement


theorem native_selectIndexed_refines {n k : ℕ} (table : BinaryStoredOverlapEnvironment.Segment n k)
    (source : RationalSegmentLottery n k) (hc : table.Canonical) (hr : table.Refines source)
    (hw : ∀ slot, 0 ≤ value (table.weight.read slot)) (fallback : Fin k) (N : ℕ) (bits : Fin N → Bool)
    (pos : ℕ) (hp : pos ≤ N) :
    BinaryCategoricalRun.runIndexed fallback N bits (.remaining (NativeBinarySegmentSampler.weights table hc hw)) pos hp =
      (categoricalMachine fallback).runCursorIndexed N bits (.state source.start) pos hp :=
  BinarySegmentCategorical.selectIndexed_refines table source hc hr fallback N bits pos hp

theorem select_resource_failure (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : Admissible input)
    (K N : ℕ) (outer : Fin K → Bool) (bits : Fin N → Bool) (hNone : (setupRun input hC N bits).1=none) :
    select input hC hAd K N outer bits = (none,(setupRun input hC N bits).2) := by
  unfold select
  split
  · rfl
  · rename_i result hs
    rw [hNone] at hs
    cases hs

theorem selected_categorical_refines (input : BinaryFourParameters.Input) (source : RationalFourInput) (hC : input.Canonical)
    (hr : input.Refines source) (hCase : source.w < (1-source.p)*source.ell) (hAd : Admissible input)
    (K N : ℕ) (outer : Fin K → Bool) (bits : Fin N → Bool)
    (result : BinaryThreeResourcePair.Certified (prepare input).capacity)
    (hSuccess : (setupRun input hC N bits).1=some result) :
    select input hC hAd K N outer bits =
      let phase := phaseResult input source hC hr hCase N bits result hSuccess
      let lottery := ((source.reflectedResourceSystem hCase).terminalData phase).profile K outer
      let chosen := (categoricalMachine (0 : Fin 18)).runCursorIndexed N bits (.state lottery.start)
        (setupRun input hC N bits).2 (setupRun_position input hC N bits)
      (chosen.1.map (fun slot => (result,slot)),chosen.2) := by
  unfold select
  split
  · rename_i hn
    rw [hSuccess] at hn
    cases hn
  · rename_i current hCurrent
    have hEqual : current=result := Option.some.inj (hCurrent.symm.trans hSuccess)
    subst current
    dsimp only
    have hRef := terminal_profile_refines input source hC hr hCase N bits result hSuccess K outer
    have he := native_selectIndexed_refines
      (BinaryTerminalProfileCompiler.profile (prepare input) result.state K outer)
      (((source.reflectedResourceSystem hCase).terminalData (phaseResult input source hC hr hCase N bits result hSuccess)).profile K outer)
      (BinaryTerminalProfileCompiler.profile_canonical _ result.state (prepare_canonical input hC) result.canonical K outer)
      hRef (profile_nonnegative input hC hAd N bits result hSuccess K outer) 0 N bits
      (setupRun input hC N bits).2 (setupRun_position input hC N bits)
    rw [he]
end Blotto.BinaryReflectedSerialSelection
