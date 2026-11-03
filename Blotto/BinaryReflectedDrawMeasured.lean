import Blotto.BinaryReflectedResourceMeasured
import Blotto.BinaryReflectedTerminalFactoryMeasured
import Blotto.BinaryReflectedTableDrawMeasured
import Blotto.BinaryReflectedDrawLifetime

/-! The actual measured reflected setup/resource result feeds one measured
terminal factory, selection and physical point/reflected emission. Reference
readers and logical source factories occur only in erased proofs. -/
namespace Blotto.BinaryReflectedDrawMeasured
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage BinaryReflectedFourSetup
set_option autoImplicit false
set_option maxHeartbeats 1500000

set_option cleanup.letToHave false in
def afterResourceWithFactoryExtras (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (hC : input.Canonical) (hAd : BinaryReflectedSerialRun.Admissible input) (cached : BinaryReflectedPreparationLifetime.Prepared input)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value)
    (resource : BinaryPRGWordControllerThreeResource.Result store (prepare input).capacity)
    (hResource : resource = BinaryPRGWordControllerThreeResource.setupIndexed store input hC pc hp)
    (K : ℕ) (outer scalar : BinaryScalarTape K) : (((BinaryPRGWordControllerReflected.Result store × Trace) × ℕ) × ℕ) × ℕ :=
  match hResult : resource.1 with
  | none => (((((none,resource.2),wrap 24 2 []),4),0),0)
  | some result =>
      have hSuccess := BinaryPRGWordControllerReflected.setup_local_success store input hC pc hp result (by rw [← hResource]; exact hResult)
      let prepared := BinaryReflectedTerminalFactoryMeasured.preparedWithExtras input hC hAd cached
        (store.cap.value-pc.value) (BinaryPRGWordControllerReflected.localReader store pc hp) result hSuccess K outer
      let terminal := prepared.1
      let produced := BinaryReflectedTableDrawMeasured.runWithExtras store input terminal.1.1 K scalar resource.2
        (by rw [hResource]; exact (BinaryPRGWordControllerThreeResource.setupIndexed_position store input hC pc hp).2)
      let drawn := produced.1
      ((((drawn.1.1,wrap 40 3 [terminal.1.2,drawn.1.2]),terminal.2+drawn.2+8),produced.2),prepared.2)

def afterResourceWithDrawExtras (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (hC : input.Canonical) (hAd : BinaryReflectedSerialRun.Admissible input) (cached : BinaryReflectedPreparationLifetime.Prepared input)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value)
    (resource : BinaryPRGWordControllerThreeResource.Result store (prepare input).capacity)
    (hResource : resource = BinaryPRGWordControllerThreeResource.setupIndexed store input hC pc hp)
    (K : ℕ) (outer scalar : BinaryScalarTape K) : ((BinaryPRGWordControllerReflected.Result store × Trace) × ℕ) × ℕ :=
  (afterResourceWithFactoryExtras store input hC hAd cached pc hp resource hResource K outer scalar).1

theorem afterResourceWithFactoryExtras_compat (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (hC : input.Canonical) (hAd : BinaryReflectedSerialRun.Admissible input) (cached : BinaryReflectedPreparationLifetime.Prepared input)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value)
    (resource : BinaryPRGWordControllerThreeResource.Result store (prepare input).capacity)
    (hResource : resource = BinaryPRGWordControllerThreeResource.setupIndexed store input hC pc hp)
    (K : ℕ) (outer scalar : BinaryScalarTape K) :
    (afterResourceWithFactoryExtras store input hC hAd cached pc hp resource hResource K outer scalar).1 = afterResourceWithDrawExtras store input hC hAd cached pc hp resource hResource K outer scalar := rfl

theorem afterResourceWithDrawExtras_record (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (hC : input.Canonical) (hAd : BinaryReflectedSerialRun.Admissible input) (cached : BinaryReflectedPreparationLifetime.Prepared input)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value)
    (resource : BinaryPRGWordControllerThreeResource.Result store (prepare input).capacity)
    (hResource : resource = BinaryPRGWordControllerThreeResource.setupIndexed store input hC pc hp)
    (K : ℕ) (outer scalar : BinaryScalarTape K) :
    afterResourceWithDrawExtras store input hC hAd cached pc hp resource hResource K outer scalar =
  match hResult : resource.1 with
  | none => ((((none,resource.2),wrap 24 2 []),4),0)
  | some result =>
      have hSuccess := BinaryPRGWordControllerReflected.setup_local_success store input hC pc hp result (by rw [← hResource]; exact hResult)
      let terminal := BinaryReflectedTerminalFactoryMeasured.prepared input hC hAd cached
        (store.cap.value-pc.value) (BinaryPRGWordControllerReflected.localReader store pc hp) result hSuccess K outer
      let produced := BinaryReflectedTableDrawMeasured.runWithExtras store input terminal.1.1 K scalar resource.2
        (by rw [hResource]; exact (BinaryPRGWordControllerThreeResource.setupIndexed_position store input hC pc hp).2)
      let drawn := produced.1
      (((drawn.1.1,wrap 40 3 [terminal.1.2,drawn.1.2]),terminal.2+drawn.2+8),produced.2) := by
  simp only [afterResourceWithDrawExtras,afterResourceWithFactoryExtras,BinaryReflectedTerminalFactoryMeasured.fromTerminalWithExtras_compat,BinaryReflectedTerminalFactoryMeasured.tableWithExtras_compat,BinaryReflectedTerminalFactoryMeasured.preparedWithExtras_compat,BinaryReflectedResourceMeasured.runWithExtras_compat]
  split <;> rfl

def afterResource (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (hC : input.Canonical) (hAd : BinaryReflectedSerialRun.Admissible input) (cached : BinaryReflectedPreparationLifetime.Prepared input)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value)
    (resource : BinaryPRGWordControllerThreeResource.Result store (prepare input).capacity)
    (hResource : resource = BinaryPRGWordControllerThreeResource.setupIndexed store input hC pc hp)
    (K : ℕ) (outer scalar : BinaryScalarTape K) : (BinaryPRGWordControllerReflected.Result store × Trace) × ℕ :=
  (afterResourceWithDrawExtras store input hC hAd cached pc hp resource hResource K outer scalar).1

theorem afterResourceWithDrawExtras_compat (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (hC : input.Canonical) (hAd : BinaryReflectedSerialRun.Admissible input) (cached : BinaryReflectedPreparationLifetime.Prepared input)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value)
    (resource : BinaryPRGWordControllerThreeResource.Result store (prepare input).capacity)
    (hResource : resource = BinaryPRGWordControllerThreeResource.setupIndexed store input hC pc hp)
    (K : ℕ) (outer scalar : BinaryScalarTape K)  :
    (afterResourceWithDrawExtras store input hC hAd cached pc hp resource hResource K outer scalar).1 = afterResource store input hC hAd cached pc hp resource hResource K outer scalar := rfl

theorem afterResource_record (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (hC : input.Canonical) (hAd : BinaryReflectedSerialRun.Admissible input) (cached : BinaryReflectedPreparationLifetime.Prepared input)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value)
    (resource : BinaryPRGWordControllerThreeResource.Result store (prepare input).capacity)
    (hResource : resource = BinaryPRGWordControllerThreeResource.setupIndexed store input hC pc hp)
    (K : ℕ) (outer scalar : BinaryScalarTape K)  :
    afterResource store input hC hAd cached pc hp resource hResource K outer scalar =
  match hResult : resource.1 with
  | none => (((none,resource.2),wrap 24 2 []),4)
  | some result =>
      have hSuccess := BinaryPRGWordControllerReflected.setup_local_success store input hC pc hp result (by rw [← hResource]; exact hResult)
      let terminal := BinaryReflectedTerminalFactoryMeasured.prepared input hC hAd cached
        (store.cap.value-pc.value) (BinaryPRGWordControllerReflected.localReader store pc hp) result hSuccess K outer
      let drawn := BinaryReflectedTableDrawMeasured.run store input terminal.1.1 K scalar resource.2
        (by rw [hResource]; exact (BinaryPRGWordControllerThreeResource.setupIndexed_position store input hC pc hp).2)
      ((drawn.1.1,wrap 40 3 [terminal.1.2,drawn.1.2]),terminal.2+drawn.2+8) := by
  simp only [afterResource,afterResourceWithDrawExtras_record]
  split <;> rfl


theorem afterResource_data (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (hC : input.Canonical) (hAd : BinaryReflectedSerialRun.Admissible input) (cached : BinaryReflectedPreparationLifetime.Prepared input)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value)
    (resource : BinaryPRGWordControllerThreeResource.Result store (prepare input).capacity)
    (hResource : resource = BinaryPRGWordControllerThreeResource.setupIndexed store input hC pc hp)
    (K : ℕ) (outer scalar : BinaryScalarTape K) :
    (afterResource store input hC hAd cached pc hp resource hResource K outer scalar).1.1 =
      (BinaryReflectedDrawLifetime.afterResourceWithTrace store input hC hAd cached pc hp resource hResource K outer scalar).1 := by
  rw [afterResource_record]
  unfold BinaryReflectedDrawLifetime.afterResourceWithTrace
  dsimp only
  split
  · rename_i hNone
    split
    · rfl
    · rename_i other hOther
      rw [hNone] at hOther
      cases hOther
  · rename_i result hSome
    split
    · rename_i hNone
      rw [hNone] at hSome
      cases hSome
    · rename_i other hOther
      have hEqual : other = result := Option.some.inj (hOther.symm.trans hSome)
      subst other
      simp only [BinaryReflectedTableDrawMeasured.run_data,BinaryReflectedTerminalFactoryMeasured.prepared_data]

def afterPrice (s K i cap : ℕ) : ℕ := BinaryReflectedTerminalFactoryMeasured.workEnvelope s K+
  BinaryReflectedTableDrawMeasured.workEnvelope (expressionHeightBudget (max s (K+2)) 68) K i cap+8

def afterEnvelope (s K i cap : ℕ) : ℕ := BinaryReflectedTerminalFactoryMeasured.envelope s K+
  BinaryReflectedTableDrawMeasured.envelope (expressionHeightBudget (max s (K+2)) 68) K i cap+64

theorem afterResource_bounds (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (source : RationalFourInput) (hC : input.Canonical) (hR : input.Refines source)
    (hCase : source.w < (1-source.p)*source.ell) (hAd : BinaryReflectedSerialRun.Admissible input)
    (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s)
    (cached : BinaryReflectedPreparationLifetime.Prepared input)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value)
    (resource : BinaryPRGWordControllerThreeResource.Result store (prepare input).capacity)
    (hResource : resource = BinaryPRGWordControllerThreeResource.setupIndexed store input hC pc hp)
    (K : ℕ) (outer scalar : BinaryScalarTape K) :
    (afterResource store input hC hAd cached pc hp resource hResource K outer scalar).2 ≤ afterPrice s K store.width store.cap.value ∧
      usage (afterResource store input hC hAd cached pc hp resource hResource K outer scalar).1.2 ≤ afterEnvelope s K store.width store.cap.value := by
  subst resource
  rw [afterResource_record]
  split
  · have hw := wrap_usage 24 2 []
    simp only [List.map_nil,List.sum_nil] at hw
    change 4 ≤ _ ∧ usage (wrap 24 2 []) ≤ _
    unfold afterPrice afterEnvelope
    exact ⟨by omega,by omega⟩
  · rename_i result hResult
    let N := store.cap.value-pc.value
    let bits := BinaryPRGWordControllerReflected.localReader store pc hp
    have hSuccess := BinaryPRGWordControllerReflected.setup_local_success store input hC pc hp result hResult
    let terminal := BinaryReflectedTerminalFactoryMeasured.prepared input hC hAd cached
      N bits result hSuccess K outer
    let target := (source.reflectedResourceSystem hCase).terminalData
      (BinaryReflectedPhaseRefinement.phaseResult input source hC hR hCase N bits result hSuccess)
    have hFactory := BinaryReflectedTerminalFactoryMeasured.prepared_bounds input source
      hC hR hCase hAd s hs hH N bits result hSuccess cached K outer
    change terminal.2 ≤ _ ∧ usage terminal.1.2 ≤ _ at hFactory
    have hTable : terminal.1.1.table = BinaryTerminalProfileCompiler.profile (prepare input) result.state K outer :=
      (BinaryReflectedTerminalFactoryMeasured.prepared_table input hC hAd cached N bits result hSuccess K outer).trans
        (BinaryReflectedTerminalFactoryMeasured.table_erasure input hC cached result K outer)
    have hRef : terminal.1.1.table.Refines (target.profile K outer) := by
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
    have hDraw := BinaryReflectedTableDrawMeasured.run_bounds store input hC terminal.1.1
      (target.profile K outer) hRef _ hs68 hHeight hLengths K scalar nextPC hNextPC
    have hw := wrap_usage 40 3 [terminal.1.2,
      (BinaryReflectedTableDrawMeasured.run store input terminal.1.1 K scalar nextPC hNextPC).1.2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change terminal.2+(BinaryReflectedTableDrawMeasured.run store input terminal.1.1 K scalar nextPC hNextPC).2+8 ≤ _ ∧ usage (wrap 40 3 [terminal.1.2,
      (BinaryReflectedTableDrawMeasured.run store input terminal.1.1 K scalar nextPC hNextPC).1.2]) ≤ _
    unfold afterPrice afterEnvelope
    exact ⟨by omega,by omega⟩

abbrev Reached (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) :=
  ((BinaryReflectedPreparationLifetime.Prepared input × BinaryPRGWordControllerThreeResource.Result store (prepare input).capacity) × Trace) × ℕ

def join (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (reached : Reached store input)
    (suffix : (BinaryPRGWordControllerReflected.Result store × Trace) × ℕ) : (BinaryPRGWordControllerReflected.Result store × Trace) × ℕ :=
  ((suffix.1.1,wrap 32 2 [reached.1.2,suffix.1.2]),reached.2+suffix.2+8)

set_option cleanup.letToHave false in
def fromReachedWithFactoryExtras (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinaryReflectedSerialRun.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) (reached : Reached store input)
    (hResource : reached.1.1.2 = BinaryPRGWordControllerThreeResource.setupIndexed store input hC pc hp) : (((BinaryPRGWordControllerReflected.Result store × Trace) × ℕ) × ℕ) × ℕ :=
  let all := afterResourceWithFactoryExtras store input hC hAd reached.1.1.1 pc hp reached.1.1.2 hResource K outer scalar
  let produced := all.1
  ((join store input reached produced.1,produced.2),all.2)

def fromReachedWithDrawExtras (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinaryReflectedSerialRun.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) (reached : Reached store input)
    (hResource : reached.1.1.2 = BinaryPRGWordControllerThreeResource.setupIndexed store input hC pc hp) : ((BinaryPRGWordControllerReflected.Result store × Trace) × ℕ) × ℕ :=
  (fromReachedWithFactoryExtras store input hC hAd K outer scalar pc hp reached hResource).1

theorem fromReachedWithFactoryExtras_compat (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinaryReflectedSerialRun.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) (reached : Reached store input)
    (hResource : reached.1.1.2 = BinaryPRGWordControllerThreeResource.setupIndexed store input hC pc hp) :
    (fromReachedWithFactoryExtras store input hC hAd K outer scalar pc hp reached hResource).1 = fromReachedWithDrawExtras store input hC hAd K outer scalar pc hp reached hResource := rfl

theorem fromReachedWithDrawExtras_record (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinaryReflectedSerialRun.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) (reached : Reached store input)
    (hResource : reached.1.1.2 = BinaryPRGWordControllerThreeResource.setupIndexed store input hC pc hp) :
    fromReachedWithDrawExtras store input hC hAd K outer scalar pc hp reached hResource =
  let produced := afterResourceWithDrawExtras store input hC hAd reached.1.1.1 pc hp reached.1.1.2 hResource K outer scalar
  (join store input reached produced.1,produced.2) := by
  simp only [fromReachedWithDrawExtras,fromReachedWithFactoryExtras,BinaryReflectedTerminalFactoryMeasured.fromTerminalWithExtras_compat,BinaryReflectedTerminalFactoryMeasured.tableWithExtras_compat,BinaryReflectedTerminalFactoryMeasured.preparedWithExtras_compat,BinaryReflectedResourceMeasured.runWithExtras_compat,afterResourceWithFactoryExtras_compat]

def fromReached (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinaryReflectedSerialRun.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) (reached : Reached store input)
    (hResource : reached.1.1.2 = BinaryPRGWordControllerThreeResource.setupIndexed store input hC pc hp) :
    (BinaryPRGWordControllerReflected.Result store × Trace) × ℕ :=
  (fromReachedWithDrawExtras store input hC hAd K outer scalar pc hp reached hResource).1

theorem fromReachedWithDrawExtras_compat (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinaryReflectedSerialRun.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) (reached : Reached store input)
    (hResource : reached.1.1.2 = BinaryPRGWordControllerThreeResource.setupIndexed store input hC pc hp)  :
    (fromReachedWithDrawExtras store input hC hAd K outer scalar pc hp reached hResource).1 = fromReached store input hC hAd K outer scalar pc hp reached hResource := rfl

theorem fromReached_record (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinaryReflectedSerialRun.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) (reached : Reached store input)
    (hResource : reached.1.1.2 = BinaryPRGWordControllerThreeResource.setupIndexed store input hC pc hp)  :
    fromReached store input hC hAd K outer scalar pc hp reached hResource =
  let suffix := afterResource store input hC hAd reached.1.1.1 pc hp reached.1.1.2 hResource K outer scalar
  join store input reached suffix := by
  rfl


set_option cleanup.letToHave false in
def runWithFactoryExtras (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinaryReflectedSerialRun.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) : (((BinaryPRGWordControllerReflected.Result store × Trace) × ℕ) × ℕ) × ℕ :=
  let reached := BinaryReflectedResourceMeasured.runWithExtras store input hC pc hp
  let all := fromReachedWithFactoryExtras store input hC hAd K outer scalar pc hp reached.1
    (by simpa only [reached,BinaryReflectedResourceMeasured.runWithExtras_compat] using BinaryReflectedResourceMeasured.run_resource store input hC pc hp)
  (all.1,reached.2+all.2)

def runWithDrawExtras (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinaryReflectedSerialRun.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) : ((BinaryPRGWordControllerReflected.Result store × Trace) × ℕ) × ℕ :=
  (runWithFactoryExtras store input hC hAd K outer scalar pc hp).1

theorem runWithFactoryExtras_compat (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinaryReflectedSerialRun.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (runWithFactoryExtras store input hC hAd K outer scalar pc hp).1 = runWithDrawExtras store input hC hAd K outer scalar pc hp := rfl

theorem runWithDrawExtras_record (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinaryReflectedSerialRun.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    runWithDrawExtras store input hC hAd K outer scalar pc hp =
  let reached := BinaryReflectedResourceMeasured.run store input hC pc hp
  fromReachedWithDrawExtras store input hC hAd K outer scalar pc hp reached (BinaryReflectedResourceMeasured.run_resource store input hC pc hp) := by
  simp only [runWithDrawExtras,runWithFactoryExtras,BinaryReflectedTerminalFactoryMeasured.fromTerminalWithExtras_compat,BinaryReflectedTerminalFactoryMeasured.tableWithExtras_compat,BinaryReflectedTerminalFactoryMeasured.preparedWithExtras_compat,BinaryReflectedResourceMeasured.runWithExtras_compat,afterResourceWithFactoryExtras_compat,fromReachedWithFactoryExtras_compat]

def run (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinaryReflectedSerialRun.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) : (BinaryPRGWordControllerReflected.Result store × Trace) × ℕ :=
  (runWithDrawExtras store input hC hAd K outer scalar pc hp).1

theorem runWithDrawExtras_compat (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinaryReflectedSerialRun.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value)  :
    (runWithDrawExtras store input hC hAd K outer scalar pc hp).1 = run store input hC hAd K outer scalar pc hp := rfl

theorem run_record (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinaryReflectedSerialRun.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value)  :
    run store input hC hAd K outer scalar pc hp =
  let reached := BinaryReflectedResourceMeasured.run store input hC pc hp
  fromReached store input hC hAd K outer scalar pc hp reached (BinaryReflectedResourceMeasured.run_resource store input hC pc hp) := by
  rfl


theorem fromReached_data (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinaryReflectedSerialRun.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) (reached : Reached store input)
    (hResource : reached.1.1.2 = BinaryPRGWordControllerThreeResource.setupIndexed store input hC pc hp) :
    (fromReached store input hC hAd K outer scalar pc hp reached hResource).1.1 =
      BinaryPRGWordControllerReflected.run store input hC hAd K outer scalar pc hp := by
  rw [fromReached_record]
  unfold join
  exact (afterResource_data store input hC hAd reached.1.1.1 pc hp reached.1.1.2 hResource K outer scalar).trans
    (BinaryReflectedDrawLifetime.afterResourceWithTrace_erasure store input hC hAd reached.1.1.1 pc hp reached.1.1.2 hResource K outer scalar)

theorem run_data (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinaryReflectedSerialRun.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (run store input hC hAd K outer scalar pc hp).1.1 = BinaryPRGWordControllerReflected.run store input hC hAd K outer scalar pc hp := by
  rw [run_record]
  apply fromReached_data

theorem run_previous (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinaryReflectedSerialRun.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (run store input hC hAd K outer scalar pc hp).1.1 = (BinaryReflectedDrawLifetime.runWithTrace store input hC hAd K outer scalar pc hp).1 :=
  (run_data store input hC hAd K outer scalar pc hp).trans (BinaryReflectedDrawLifetime.runWithTrace_erasure store input hC hAd K outer scalar pc hp).symm

theorem run_position (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinaryReflectedSerialRun.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    pc.value ≤ (run store input hC hAd K outer scalar pc hp).1.1.2.value ∧
      (run store input hC hAd K outer scalar pc hp).1.1.2.value ≤ store.cap.value := by
  rw [run_data]
  exact BinaryPRGWordControllerReflected.run_position store input hC hAd K outer scalar pc hp

def workEnvelope (s K i cap : ℕ) : ℕ := BinaryReflectedResourceMeasured.workEnvelope s i cap+afterPrice s K i cap+8

def envelope (s K i cap : ℕ) : ℕ := BinaryReflectedResourceMeasured.envelope s i cap+afterEnvelope s K i cap+64

theorem join_bounds (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (reached : Reached store input)
    (suffix : (BinaryPRGWordControllerReflected.Result store × Trace) × ℕ) (R S U F : ℕ)
    (hr : reached.2 ≤ R ∧ usage reached.1.2 ≤ U) (hs : suffix.2 ≤ S ∧ usage suffix.1.2 ≤ F) :
    (join store input reached suffix).2 ≤ R+S+8 ∧ usage (join store input reached suffix).1.2 ≤ U+F+64 := by
  have hw := wrap_usage 32 2 [reached.1.2,suffix.1.2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change reached.2+suffix.2+8 ≤ _ ∧ usage (wrap 32 2 [reached.1.2,suffix.1.2]) ≤ _
  exact ⟨by omega,by omega⟩

theorem fromReached_bounds (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1-source.p)*source.ell) (hAd : BinaryReflectedSerialRun.Admissible input)
    (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) (reached : Reached store input)
    (hResource : reached.1.1.2 = BinaryPRGWordControllerThreeResource.setupIndexed store input hC pc hp)
    (hReached : reached.2 ≤ BinaryReflectedResourceMeasured.workEnvelope s store.width store.cap.value ∧
      usage reached.1.2 ≤ BinaryReflectedResourceMeasured.envelope s store.width store.cap.value) :
    (fromReached store input hC hAd K outer scalar pc hp reached hResource).2 ≤ workEnvelope s K store.width store.cap.value ∧
      usage (fromReached store input hC hAd K outer scalar pc hp reached hResource).1.2 ≤ envelope s K store.width store.cap.value := by
  let suffix := afterResource store input hC hAd reached.1.1.1 pc hp reached.1.1.2 hResource K outer scalar
  have hSuffix := afterResource_bounds store input source hC hR hCase hAd s hs hH reached.1.1.1 pc hp reached.1.1.2 hResource K outer scalar
  have hResult := join_bounds store input reached suffix _ _ _ _ hReached hSuffix
  rw [fromReached_record]
  unfold workEnvelope envelope
  with_reducible exact hResult

theorem run_bounds (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1-source.p)*source.ell) (hAd : BinaryReflectedSerialRun.Admissible input)
    (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (run store input hC hAd K outer scalar pc hp).2 ≤ workEnvelope s K store.width store.cap.value ∧
      usage (run store input hC hAd K outer scalar pc hp).1.2 ≤ envelope s K store.width store.cap.value := by
  have hResult := fromReached_bounds store input source hC hR hCase hAd s hs hH K outer scalar pc hp _
    (BinaryReflectedResourceMeasured.run_resource store input hC pc hp) (BinaryReflectedResourceMeasured.run_bounds store input source hC hR hCase s hs hH pc hp)
  rw [run_record]
  with_reducible exact hResult

theorem all_prefix (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1-source.p)*source.ell) (hAd : BinaryReflectedSerialRun.Admissible input)
    (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) (borrowed steps : ℕ) :
    retainedHeap borrowed (run store input hC hAd K outer scalar pc hp).1.2 steps ≤ borrowed+envelope s K store.width store.cap.value ∧
      framePeak ((run store input hC hAd K outer scalar pc hp).1.2.take steps) ≤ envelope s K store.width store.cap.value :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (run_bounds store input source hC hR hCase hAd s hs hH K outer scalar pc hp).2 borrowed steps

end Blotto.BinaryReflectedDrawMeasured
