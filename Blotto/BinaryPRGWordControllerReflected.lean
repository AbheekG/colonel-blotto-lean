import Blotto.BinaryPRGWordControllerThreeResource
import Blotto.BinaryPRGWordControllerDataCategorical
import Blotto.BinaryPRGWordControllerWindow
import Blotto.BinaryReflectedIndexedRun

/-! Reflected resource reduction and its 18-slot categorical continuation keep
one whole concrete Store, cap and absolute Boolean counter. Local windows and
numeric positions occur solely in proof/reference code. Exact old selected
state/slot, output bytes, exhaustion and absolute position are preserved.
Original profile/emission arithmetic, arrays/copies and complete bit-machine
cost/space composition remain distinct further joins. -/

namespace Blotto.BinaryPRGWordControllerReflected
open BinarySeedLookupTree BinaryRationalNormalization BinaryRationalEncoding
open BinaryReflectedFourSetup BinaryReflectedSerialRun

/-- This reader belongs exclusively to the old-window proof specification. -/
def localReader (store : Store) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    Fin (store.cap.value - pc.value) → Bool :=
  WordStateMachine.inputWindow (BinaryWordIndexCoinController.reader store) pc.value
    (store.cap.value - pc.value) (by omega)

theorem setup_local_success (store : Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value)
    (result : BinaryThreeResourcePair.Certified (prepare input).capacity)
    (h : (BinaryPRGWordControllerThreeResource.setupIndexed store input hC pc hp).1 = some result) :
    (BinarySharedResourceRun.setupRun input hC (store.cap.value - pc.value) (localReader store pc hp)).1 = some result := by
  have he := congrArg Prod.fst (BinaryPRGWordControllerThreeResource.setupIndexed_state store input hC pc hp)
  exact he.symm.trans h

abbrev Selection (store : Store) (input : BinaryFourParameters.Input) :=
  Option (BinaryThreeResourcePair.Certified (prepare input).capacity × Fin 18) × FixedBinaryWord store.width

def select (store : Store) (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : Admissible input)
    (K : ℕ) (outer : Fin K → Bool) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    Selection store input :=
  let reached := BinaryPRGWordControllerThreeResource.setupIndexed store input hC pc hp
  match hResult : reached.1 with
  | none => (none,reached.2)
  | some result =>
      let table := BinaryTerminalProfileCompiler.profile (prepare input) result.state K outer
      let weights := NativeBinarySegmentSampler.weights table
        (BinaryTerminalProfileCompiler.profile_canonical _ result.state (prepare_canonical input hC) result.canonical K outer)
        (profile_nonnegative input hC hAd (store.cap.value - pc.value) (localReader store pc hp) result
          (setup_local_success store input hC pc hp result hResult) K outer)
      let chosen := BinaryPRGWordControllerDataCategorical.run store (0 : Fin 18) weights reached.2
        (BinaryPRGWordControllerThreeResource.setupIndexed_position store input hC pc hp).2
      (chosen.1.map (fun slot => (result,slot)),chosen.2)

def decodedSelection (store : Store) (input : BinaryFourParameters.Input) (result : Selection store input) :
    Option (BinaryThreeResourcePair.Certified (prepare input).capacity × Fin 18) × ℕ :=
  (result.1,result.2.value)

set_option maxHeartbeats 1000000 in
theorem select_state (store : Store) (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : Admissible input)
    (K : ℕ) (outer : Fin K → Bool) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    decodedSelection store input (select store input hC hAd K outer pc hp) =
      WordStateMachine.offsetConsumed pc.value (BinaryReflectedCachedRun.select input hC hAd K
        (store.cap.value - pc.value) outer (localReader store pc hp)) := by
  have hResource := BinaryPRGWordControllerThreeResource.setupIndexed_state store input hC pc hp
  have hOption := congrArg Prod.fst hResource
  have hPosition := congrArg Prod.snd hResource
  change (BinaryPRGWordControllerThreeResource.setupIndexed store input hC pc hp).1 =
    (BinarySharedResourceRun.setupRun input hC (store.cap.value - pc.value) (localReader store pc hp)).1 at hOption
  change (BinaryPRGWordControllerThreeResource.setupIndexed store input hC pc hp).2.value =
    pc.value + (BinarySharedResourceRun.setupRun input hC (store.cap.value - pc.value) (localReader store pc hp)).2 at hPosition
  unfold select BinaryReflectedCachedRun.select
  dsimp only
  split
  · rename_i hReached
    have hOld := hOption.symm.trans hReached
    split
    · simp only [decodedSelection,WordStateMachine.offsetConsumed,hPosition]
    · rename_i other hOther
      cases hOther.symm.trans hOld
  · rename_i result hReached
    have hOld := hOption.symm.trans hReached
    split
    · rename_i hNone
      cases hNone.symm.trans hOld
    · rename_i other hOther
      have hSame : other = result := Option.some.inj (hOther.symm.trans hOld)
      subst other
      let table := BinaryTerminalProfileCompiler.profile (prepare input) result.state K outer
      let weights := NativeBinarySegmentSampler.weights table
        (BinaryTerminalProfileCompiler.profile_canonical _ result.state (prepare_canonical input hC) result.canonical K outer)
        (profile_nonnegative input hC hAd (store.cap.value - pc.value) (localReader store pc hp) result
          (setup_local_success store input hC pc hp result hReached) K outer)
      have hGlobal := BinaryPRGWordControllerCategorical.run_state store (0 : Fin 18) weights
        (BinaryPRGWordControllerThreeResource.setupIndexed store input hC pc hp).2
        (BinaryPRGWordControllerThreeResource.setupIndexed_position store input hC pc hp).2
      simp only [BinaryPRGWordControllerCategorical.decoded,BinaryPRGWordControllerDataCategorical.run_erasure] at hGlobal
      have hLocalPosition := setupRun_position input hC (store.cap.value - pc.value) (localReader store pc hp)
      have hWindow := BinaryPRGWordControllerWindow.categorical_offset (0 : Fin 18)
        store.cap.value (store.cap.value - pc.value) pc.value (by omega)
        (BinaryWordIndexCoinController.reader store) (localReader store pc hp) (by intro index; rfl)
        (.remaining weights)
        (BinaryPRGWordControllerThreeResource.setupIndexed store input hC pc hp).2.value
        (BinarySharedResourceRun.setupRun input hC (store.cap.value - pc.value) (localReader store pc hp)).2
        (BinaryPRGWordControllerThreeResource.setupIndexed_position store input hC pc hp).2 hLocalPosition hPosition
      have hChosen := hGlobal.trans hWindow
      have hMapped := congrArg (fun choice : Option (Fin 18) × ℕ =>
        (choice.1.map (fun slot => (result,slot)),choice.2)) hChosen
      exact hMapped

abbrev Result (store : Store) := Option (FixedArrayTable 4 SignedWord) × FixedBinaryWord store.width

def run (store : Store) (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : Admissible input)
    (K : ℕ) (outer scalar : Fin K → Bool) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) : Result store :=
  let selected := select store input hC hAd K outer pc hp
  (selected.1.map (fun pair => BinaryReflectedTerminalEmission.sample input pair.1.state K outer scalar pair.2),selected.2)

def decoded (store : Store) (result : Result store) : Option (FixedArrayTable 4 SignedWord) × ℕ :=
  (result.1,result.2.value)

set_option maxHeartbeats 800000 in
theorem run_state (store : Store) (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : Admissible input)
    (K : ℕ) (outer scalar : Fin K → Bool) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    decoded store (run store input hC hAd K outer scalar pc hp) =
      BinaryReflectedIndexedRun.run input hC hAd K store.cap.value outer scalar
        (BinaryWordIndexCoinController.reader store) pc.value hp := by
  have h := select_state store input hC hAd K outer pc hp
  have hm := congrArg (fun selected : Option (BinaryThreeResourcePair.Certified (prepare input).capacity × Fin 18) × ℕ =>
    (selected.1.map (fun pair => BinaryReflectedTerminalEmission.sample input pair.1.state K outer scalar pair.2),selected.2)) h
  exact hm

set_option maxHeartbeats 1000000 in
theorem run_position (store : Store) (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : Admissible input)
    (K : ℕ) (outer scalar : Fin K → Bool) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    pc.value ≤ (run store input hC hAd K outer scalar pc hp).2.value ∧
      (run store input hC hAd K outer scalar pc hp).2.value ≤ store.cap.value := by
  unfold run select
  dsimp only
  split
  · exact BinaryPRGWordControllerThreeResource.setupIndexed_position store input hC pc hp
  · rename_i result hReached
    dsimp only
    rw [← BinaryPRGWordControllerDataCategorical.run_erasure]
    have hPrefix := BinaryPRGWordControllerThreeResource.setupIndexed_position store input hC pc hp
    let table := BinaryTerminalProfileCompiler.profile (prepare input) result.state K outer
    let weights := NativeBinarySegmentSampler.weights table
      (BinaryTerminalProfileCompiler.profile_canonical _ result.state (prepare_canonical input hC) result.canonical K outer)
      (profile_nonnegative input hC hAd (store.cap.value - pc.value) (localReader store pc hp) result
        (setup_local_success store input hC pc hp result hReached) K outer)
    have hLater := BinaryPRGWordControllerCategorical.run_position_bounds store (0 : Fin 18) weights
      (BinaryPRGWordControllerThreeResource.setupIndexed store input hC pc hp).2 hPrefix.2
    exact ⟨hPrefix.1.trans hLater.1,hLater.2⟩

def fixedSample (store : Store) (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : Admissible input)
    (K : ℕ) (outer scalar : Fin K → Bool) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    FixedArrayTable 4 SignedWord × FixedBinaryWord store.width :=
  let result := run store input hC hAd K outer scalar pc hp
  (result.1.getD (BinaryTerminalFallback.sample input hC hAd K outer scalar),result.2)

theorem fixedSample_state (store : Store) (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : Admissible input)
    (K : ℕ) (outer scalar : Fin K → Bool) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (fixedSample store input hC hAd K outer scalar pc hp).1 =
      (BinaryReflectedIndexedRun.run input hC hAd K store.cap.value outer scalar
        (BinaryWordIndexCoinController.reader store) pc.value hp).1.getD
        (BinaryTerminalFallback.sample input hC hAd K outer scalar) := by
  unfold fixedSample
  have h := congrArg Prod.fst (run_state store input hC hAd K outer scalar pc hp)
  exact congrArg (fun row => row.getD (BinaryTerminalFallback.sample input hC hAd K outer scalar)) h

end Blotto.BinaryPRGWordControllerReflected
