import Blotto.BinaryScalarTape
import Blotto.BinaryReflectedTableDrawLifetime
import Blotto.BinaryPRGHeapReflectedLifetime

/-! Complete reflected resource/factory/selection/emission execution. The actual
physical resource result and retained setup feed one terminal factory and one
shared-cap draw; all reference calls and source witnesses occur only in proofs. -/
namespace Blotto.BinaryReflectedDrawLifetime
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGHeapTraceUsage BinaryReflectedFourSetup
set_option maxHeartbeats 2000000

def afterResourceWithTrace (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (hC : input.Canonical) (hAd : BinaryReflectedSerialRun.Admissible input)
    (cached : BinaryReflectedPreparationLifetime.Prepared input)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value)
    (resource : BinaryPRGWordControllerThreeResource.Result store (prepare input).capacity)
    (hResource : resource = BinaryPRGWordControllerThreeResource.setupIndexed store input hC pc hp)
    (K : ℕ) (outer scalar : BinaryScalarTape K) : BinaryPRGWordControllerReflected.Result store × Trace :=
  match hResult : resource.1 with
  | none => ((none,resource.2),wrap 24 2 [])
  | some result =>
      have hSuccess := BinaryPRGWordControllerReflected.setup_local_success store input hC pc hp result
        (by rw [← hResource]; exact hResult)
      let terminal := BinaryReflectedTerminalFactoryLifetime.preparedWithTrace input hC hAd cached
        (store.cap.value-pc.value) (BinaryPRGWordControllerReflected.localReader store pc hp)
        result hSuccess K outer
      let drawn := BinaryReflectedTableDrawLifetime.runWithTrace store input terminal.1 K scalar resource.2
        (by rw [hResource]; exact (BinaryPRGWordControllerThreeResource.setupIndexed_position store input hC pc hp).2)
      (drawn.1,wrap 40 3 [terminal.2,drawn.2])

theorem afterResourceWithTrace_erasure (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (hC : input.Canonical) (hAd : BinaryReflectedSerialRun.Admissible input)
    (cached : BinaryReflectedPreparationLifetime.Prepared input)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value)
    (resource : BinaryPRGWordControllerThreeResource.Result store (prepare input).capacity)
    (hResource : resource = BinaryPRGWordControllerThreeResource.setupIndexed store input hC pc hp)
    (K : ℕ) (outer scalar : BinaryScalarTape K) :
    (afterResourceWithTrace store input hC hAd cached pc hp resource hResource K outer scalar).1 =
      BinaryPRGWordControllerReflected.run store input hC hAd K outer scalar pc hp := by
  subst resource
  unfold afterResourceWithTrace
  split
  · rename_i hNone
    unfold BinaryPRGWordControllerReflected.run BinaryPRGWordControllerReflected.select
    dsimp only
    split
    · rfl
    · rename_i result hSome
      rw [hNone] at hSome
      cases hSome
  · rename_i result hSome
    unfold BinaryPRGWordControllerReflected.run BinaryPRGWordControllerReflected.select
    dsimp only
    rw [BinaryReflectedTableDrawLifetime.runWithTrace_erasure store input hC,
      BinaryReflectedTerminalFactoryLifetime.preparedWithTrace_erasure]
    unfold BinaryReflectedTableDrawLifetime.oldRun BinaryReflectedCategoricalWork.prepared
      BinaryReflectedTerminalEmission.sample
    split
    · rename_i hNone
      rw [hSome] at hNone
      cases hNone
    · rename_i current hCurrent
      have hEqual : current = result := Option.some.inj (hCurrent.symm.trans hSome)
      subst current
      simp only [Option.map_map,Function.comp_def]

def afterEnvelope (s K indexWidth seedCap : ℕ) : ℕ :=
  BinaryReflectedTerminalFactoryLifetime.envelope s K +
    BinaryReflectedTableDrawLifetime.envelope (expressionHeightBudget (max s (K+2)) 68)
      K indexWidth seedCap + 128

theorem afterResourceWithTrace_usage (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (source : RationalFourInput) (hC : input.Canonical) (hR : input.Refines source)
    (hCase : source.w < (1-source.p)*source.ell) (hAd : BinaryReflectedSerialRun.Admissible input)
    (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s)
    (cached : BinaryReflectedPreparationLifetime.Prepared input)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value)
    (resource : BinaryPRGWordControllerThreeResource.Result store (prepare input).capacity)
    (hResource : resource = BinaryPRGWordControllerThreeResource.setupIndexed store input hC pc hp)
    (K : ℕ) (outer scalar : BinaryScalarTape K) :
    usage (afterResourceWithTrace store input hC hAd cached pc hp resource hResource K outer scalar).2 ≤
      afterEnvelope s K store.width store.cap.value := by
  subst resource
  unfold afterResourceWithTrace
  split
  · have hw := wrap_usage 24 2 []
    simp only [List.map_nil,List.sum_nil] at hw
    change usage (wrap 24 2 []) ≤ _
    unfold afterEnvelope
    omega
  · rename_i result hResult
    let N := store.cap.value-pc.value
    let bits := BinaryPRGWordControllerReflected.localReader store pc hp
    have hSuccess := BinaryPRGWordControllerReflected.setup_local_success store input hC pc hp result hResult
    let terminal := BinaryReflectedTerminalFactoryLifetime.preparedWithTrace input hC hAd cached
      N bits result hSuccess K outer
    let target := (source.reflectedResourceSystem hCase).terminalData
      (BinaryReflectedPhaseRefinement.phaseResult input source hC hR hCase N bits result hSuccess)
    have hFactory := BinaryReflectedTerminalFactoryLifetime.tableWithTrace_usage input source
      hC hR hCase s hs hH N bits result hSuccess cached K outer
    change usage terminal.2 ≤ _ at hFactory
    have hTerminalState := BinaryReflectedTerminalFactoryLifetime.preparedWithTrace_erasure input
      hC hAd cached N bits result hSuccess K outer
    have hTable : terminal.1.table = BinaryTerminalProfileCompiler.profile (prepare input) result.state K outer :=
      congrArg BinaryStoredSegmentProgram.Prepared.table hTerminalState
    have hRef : terminal.1.table.Refines (target.profile K outer) := by
      rw [hTable]
      exact BinaryReflectedPhaseRefinement.terminal_profile_refines input source hC hR hCase
        N bits result hSuccess K outer
    have hHeight := BinaryReflectedReachedHeight.profile_height input source hC hR hCase
      s hs hH N bits result hSuccess K outer
    have hLengths : ∀ j,RationalHeight (value ((originalLengths input).read j))
        (expressionHeightBudget (max s (K+2)) 68) := by
      intro j
      rw [originalLengths_value input source hR j]
      exact (hH.originalLengths j).mono
        ((le_max_left s (K+2)).trans (expressionHeightBudget_ge_input _ 68))
    have hs68 : 3 ≤ expressionHeightBudget (max s (K+2)) 68 := by
      unfold expressionHeightBudget
      omega
    let nextPC := (BinaryPRGWordControllerThreeResource.setupIndexed store input hC pc hp).2
    have hNextPC : nextPC.value ≤ store.cap.value :=
      (BinaryPRGWordControllerThreeResource.setupIndexed_position store input hC pc hp).2
    have hDraw := BinaryReflectedTableDrawLifetime.runWithTrace_usage store input hC terminal.1
      (target.profile K outer) hRef _ hs68 hHeight hLengths K scalar nextPC hNextPC
    have hw := wrap_usage 40 3 [terminal.2,
      (BinaryReflectedTableDrawLifetime.runWithTrace store input terminal.1 K scalar nextPC hNextPC).2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change usage (wrap 40 3 [terminal.2,
      (BinaryReflectedTableDrawLifetime.runWithTrace store input terminal.1 K scalar nextPC hNextPC).2]) ≤ _
    unfold afterEnvelope
    omega

def runWithTrace (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (hC : input.Canonical) (hAd : BinaryReflectedSerialRun.Admissible input)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width)
    (hp : pc.value ≤ store.cap.value) : BinaryPRGWordControllerReflected.Result store × Trace :=
  let reached := BinaryPRGHeapReflectedLifetime.runWithTrace store input hC pc hp
  have hResource : reached.1.2 = BinaryPRGWordControllerThreeResource.setupIndexed store input hC pc hp :=
    (BinaryPRGHeapReflectedLifetime.runWithTrace_erasure store input hC pc hp).trans
      (BinaryPRGHeapReflectedSetup.run_erasure store input hC pc hp)
  let suffix := afterResourceWithTrace store input hC hAd reached.1.1 pc hp reached.1.2 hResource K outer scalar
  (suffix.1,wrap 32 2 [reached.2,suffix.2])

theorem runWithTrace_erasure (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (hC : input.Canonical) (hAd : BinaryReflectedSerialRun.Admissible input)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (runWithTrace store input hC hAd K outer scalar pc hp).1 =
      BinaryPRGWordControllerReflected.run store input hC hAd K outer scalar pc hp :=
  afterResourceWithTrace_erasure store input hC hAd _ pc hp _ _ K outer scalar

theorem runWithTrace_position (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (hC : input.Canonical) (hAd : BinaryReflectedSerialRun.Admissible input)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    pc.value ≤ (runWithTrace store input hC hAd K outer scalar pc hp).1.2.value ∧
      (runWithTrace store input hC hAd K outer scalar pc hp).1.2.value ≤ store.cap.value := by
  rw [runWithTrace_erasure]
  exact BinaryPRGWordControllerReflected.run_position store input hC hAd K outer scalar pc hp

def envelope (s K indexWidth seedCap : ℕ) : ℕ :=
  BinaryPRGHeapReflectedLifetime.envelope s indexWidth seedCap + afterEnvelope s K indexWidth seedCap + 128

theorem runWithTrace_usage (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (source : RationalFourInput) (hC : input.Canonical) (hR : input.Refines source)
    (hCase : source.w < (1-source.p)*source.ell) (hAd : BinaryReflectedSerialRun.Admissible input)
    (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    usage (runWithTrace store input hC hAd K outer scalar pc hp).2 ≤ envelope s K store.width store.cap.value := by
  let reached := BinaryPRGHeapReflectedLifetime.runWithTrace store input hC pc hp
  have hResource : reached.1.2 = BinaryPRGWordControllerThreeResource.setupIndexed store input hC pc hp :=
    (BinaryPRGHeapReflectedLifetime.runWithTrace_erasure store input hC pc hp).trans
      (BinaryPRGHeapReflectedSetup.run_erasure store input hC pc hp)
  have hReached := BinaryPRGHeapReflectedLifetime.runWithTrace_usage store input source hC hR hCase s hs hH pc hp
  change usage reached.2 ≤ _ at hReached
  have hSuffix := afterResourceWithTrace_usage store input source hC hR hCase hAd s hs hH
    reached.1.1 pc hp reached.1.2 hResource K outer scalar
  have hw := wrap_usage 32 2 [reached.2,
    (afterResourceWithTrace store input hC hAd reached.1.1 pc hp reached.1.2 hResource K outer scalar).2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change usage (wrap 32 2 [reached.2,
    (afterResourceWithTrace store input hC hAd reached.1.1 pc hp reached.1.2 hResource K outer scalar).2]) ≤ _
  unfold envelope
  omega

theorem all_prefix (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (source : RationalFourInput) (hC : input.Canonical) (hR : input.Refines source)
    (hCase : source.w < (1-source.p)*source.ell) (hAd : BinaryReflectedSerialRun.Admissible input)
    (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value)
    (borrowed steps : ℕ) :
    retainedHeap borrowed (runWithTrace store input hC hAd K outer scalar pc hp).2 steps ≤
      borrowed + envelope s K store.width store.cap.value ∧
    framePeak ((runWithTrace store input hC hAd K outer scalar pc hp).2.take steps) ≤ envelope s K store.width store.cap.value :=
  BinaryPRGHeapTraceUsage.all_prefix _ _
    (runWithTrace_usage store input source hC hR hCase hAd s hs hH K outer scalar pc hp) borrowed steps

end Blotto.BinaryReflectedDrawLifetime
