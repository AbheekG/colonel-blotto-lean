import Blotto.BinaryReflectedReachedHeight
import Blotto.BinaryStoredSegmentChoiceWork
import Blotto.BinaryReflectedSerialRun

/-! The actual successful reflected terminal table supplies its eighteen
stored weights to the measured categorical selector under the same reader/cap.
Source-derived reached profile heights price probability/mass/coin operations.
Resource execution, profile factory and selected emission are separate costs. -/

namespace Blotto.BinaryReflectedCategoricalWork
open BinaryRationalNormalization BinaryRationalEncoding BinaryReflectedFourSetup
open BinarySharedResourceRun BinaryReflectedSerialRun BinaryReflectedPhaseRefinement

def prepared (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : Admissible input)
    (N : ℕ) (bits : Fin N → Bool) (result : BinaryThreeResourcePair.Certified (prepare input).capacity)
    (hSuccess : (setupRun input hC N bits).1 = some result) (K : ℕ) (outer : Fin K → Bool) :
    BinaryStoredSegmentProgram.Prepared 3 18 :=
  ⟨BinaryTerminalProfileCompiler.profile (prepare input) result.state K outer,
    BinaryTerminalProfileCompiler.profile_canonical _ result.state (prepare_canonical input hC) result.canonical K outer,
    profile_nonnegative input hC hAd N bits result hSuccess K outer⟩

def selectIndexedWithWork (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : Admissible input)
    (N : ℕ) (bits : Fin N → Bool) (result : BinaryThreeResourcePair.Certified (prepare input).capacity)
    (hSuccess : (setupRun input hC N bits).1 = some result) (K : ℕ) (outer : Fin K → Bool)
    (pos : ℕ) (hp : pos ≤ N) : (Option (Fin 18) × ℕ) × ℕ :=
  BinaryStoredSegmentChoiceWork.selectIndexedWork (prepared input hC hAd N bits result hSuccess K outer) 0 N bits pos hp

theorem selectIndexedWithWork_state (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : Admissible input)
    (N : ℕ) (bits : Fin N → Bool) (result : BinaryThreeResourcePair.Certified (prepare input).capacity)
    (hSuccess : (setupRun input hC N bits).1 = some result) (K : ℕ) (outer : Fin K → Bool)
    (pos : ℕ) (hp : pos ≤ N) :
    (selectIndexedWithWork input hC hAd N bits result hSuccess K outer pos hp).1 =
      (prepared input hC hAd N bits result hSuccess K outer).selectIndexed 0 N bits pos hp :=
  BinaryStoredSegmentChoiceWork.selectIndexedWork_state _ 0 N bits pos hp

def bound (s K remaining : ℕ) : ℕ :=
  BinaryStoredSegmentChoiceWork.selectionBound 18 (expressionHeightBudget (max s (K + 2)) 68) remaining

theorem selectIndexedWithWork_bound (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1 - source.p) * source.ell)
    (hAd : Admissible input) (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s)
    (N : ℕ) (bits : Fin N → Bool) (result : BinaryThreeResourcePair.Certified (prepare input).capacity)
    (hSuccess : (setupRun input hC N bits).1 = some result) (K : ℕ) (outer : Fin K → Bool)
    (pos : ℕ) (hp : pos ≤ N) :
    (selectIndexedWithWork input hC hAd N bits result hSuccess K outer pos hp).2 ≤ bound s K (N - pos) := by
  have hRef := terminal_profile_refines input source hC hR hCase N bits result hSuccess K outer
  have hHeight := BinaryReflectedReachedHeight.profile_height input source hC hR hCase s hs hH N bits result hSuccess K outer
  exact BinaryStoredSegmentChoiceWork.selectIndexedWork_bound (prepared input hC hAd N bits result hSuccess K outer)
    _ hRef _ hHeight.1 0 N bits pos hp

end Blotto.BinaryReflectedCategoricalWork
