import Blotto.BinaryCompleteInitialEmission
import Blotto.BinaryResourceEmissionContinuation

/-! The concrete initializer resource backend and its complete sampler instance.
All preceding complete records and both earlier cache/calculator prices are
preserved. The additional price comes from actual readback/scan/wrapper emitters;
no supplied oracle or backend premise remains in this instance. -/
namespace Blotto.BinaryCompleteInitialRequest
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryPRGPhysicalRawRequestLifetime (Request)
open BinaryTerminalPhysicalAllowanceCache (PhysicalRequest Parsed)
open BinaryPhysicalHeapAllowanceInitial (sourceAt_cap)
set_option autoImplicit false
set_option maxHeartbeats 2500000
variable {n : ℕ}

def nativeAtWithEmission (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :=
  let selected := BinaryPRGResourceWork.resourceInput request.logical.request rich
  let supplied := BinaryCompleteInitialEmission.sourceAtTraceWithWrites seed request rich pc hp
  let child := supplied.1
  let returned := child.1
  let produced := returned.1
  let drawn := produced.1.1
  match drawn.1.1.1.2.1 with
  | none =>
      let plan := BinaryTracePlanMeasured.Plan.join (.block [.frames 2,.arrayAllocation 16])
        (.shifted 2 drawn.1.2)
      let emitted := BinaryTracePlanMeasured.emitFull plan []
      (((((((((none,drawn.1.1.1.2.2),drawn.1.1.2),emitted.1.1),drawn.2+2),
        (produced.1.2,produced.2)),returned.2),emitted.1.2+emitted.2),child.2),supplied.2)
  | some state =>
      let terminal := BinaryHeapMaterializationPlan.materializeAt selected.length
        (BinaryPRGWordControllerBooleanResourceSource.capacityTable selected.length)
        drawn.1.1.1.1 (by simpa only [drawn,produced,returned,child,supplied,BinaryCompleteInitialEmission.sourceAtTraceWithWrites_compat,
          BinaryAllowanceEmissionInitial.sourceAtTraceWithWrites_compat,
          BinaryPhysicalHeapAllowanceInitial.sourceAt,BinaryPhysicalHeapAllowanceInitial.sourceAtMeasured,
          BinaryPhysicalHeapAllowanceInitial.sourceAtTraceMeasured]
          using sourceAt_cap seed request rich pc hp) state 2
      let plan := BinaryTracePlanMeasured.Plan.join (.block [.frames 2,.arrayAllocation 24])
        (.join (.shifted 2 drawn.1.2) terminal.1.2)
      let emitted := BinaryTracePlanMeasured.emitFull plan []
      (((((((((some terminal.1.1,drawn.1.1.1.2.2),drawn.1.1.2),
        emitted.1.1),drawn.2+terminal.2+4),
          (produced.1.2,produced.2)),returned.2),emitted.1.2+emitted.2),child.2),supplied.2)

theorem nativeAtWithEmission_compat (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (nativeAtWithEmission seed request rich pc hp).1 =
      BinaryAllowanceEmissionRequest.nativeAtWithEmission seed request rich pc hp := by
  simp only [nativeAtWithEmission,BinaryAllowanceEmissionRequest.nativeAtWithEmission,
    BinaryCompleteInitialEmission.sourceAtTraceWithWrites_compat]
  split
  · rename_i hNone
    simp only [hNone]
  · rename_i state hSome
    simp only [hSome]

theorem nativeAtWithEmission_bound (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (nativeAtWithEmission seed request rich pc hp).2 ≤
      70*(nativeAtWithEmission seed request rich pc hp).1.1.1.1.1.1.2.length+94 := by
  have h := BinaryCompleteInitialEmission.sourceAtTraceWithWrites_bound seed request rich pc hp
  unfold nativeAtWithEmission
  dsimp only
  split <;> simp only [BinaryTracePlanMeasured.emitFull_erases,BinaryTracePlanMeasured.emit_length,
    BinaryTracePlanMeasured.payload,List.length_cons,List.length_nil,Nat.add_zero] <;> omega

def runWithCharges (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool) :=
  let supplied := nativeAtWithEmission seed request rich (BinaryWordIndexCoinController.zeroIndex seed)
    (by rw [BinaryWordIndexCoinController.zeroIndex_value]; omega)
  let child := supplied.1
  let returned := child.1
  let drawn := returned.1.1.1
  let width := seed.cap.bits.length
  let plan := BinaryTracePlanMeasured.Plan.join
    (.block [.listAllocation width,.frames (width+2),.arrayAllocation 16,.frames 4,.arrayAllocation 24])
    (.shifted 4 drawn.1.2)
  let emitted := BinaryTracePlanMeasured.emitFull plan []
  (((((drawn.1.1,emitted.1.1),drawn.2+
      BinaryPhysicalNumericalReadbackLifetime.pairLookupAllowance request+
      BinaryPhysicalHeapRequestLifetime.preparationResidualAllowance request),
    (⟨returned.1.1.2.1,returned.1.1.2.2,returned.1.2,returned.2,emitted.1.2+emitted.2⟩ : BinaryExecutionCharges.Charges)),child.2),supplied.2)

theorem runWithCharges_compat (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool) :
    (runWithCharges seed request rich).1 = BinaryAllowanceEmissionRequest.runWithCharges seed request rich := by
  simp only [runWithCharges,BinaryAllowanceEmissionRequest.runWithCharges,nativeAtWithEmission_compat]

theorem runWithCharges_bound (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool) :
    (runWithCharges seed request rich).2 ≤ 70*(runWithCharges seed request rich).1.1.1.1.2.length+94 := by
  have h := nativeAtWithEmission_bound seed request rich (BinaryWordIndexCoinController.zeroIndex seed)
    (by rw [BinaryWordIndexCoinController.zeroIndex_value]; omega)
  simp only [runWithCharges,BinaryTracePlanMeasured.emitFull_erases,BinaryTracePlanMeasured.emit_length,
    BinaryTracePlanMeasured.payload,List.length_cons,List.length_nil,Nat.add_zero]
  omega

def backend : BinaryResourceEmissionContinuation.Backend ℕ where
  run := runWithCharges
  compat := runWithCharges_compat

def cache (parsed : PhysicalRequest) (seed : BinarySeedLookupTree.Store) (rich : Bool) :
    (((((Option (BinaryPRGHeapCachedPrefixLifetime.CachedResult
      parsed.2.logical.request rich) × FixedBinaryWord seed.width) × List Bool) × Trace) × ℕ) ×
      BinaryExecutionCharges.Charges) × ((ℕ × ℕ) × ℕ) :=
  BinaryResourceEmissionContinuation.cache backend parsed seed rich

theorem cache_compat (parsed : PhysicalRequest) (seed : BinarySeedLookupTree.Store) (rich : Bool) :
    (cache parsed seed rich).1 = BinaryTerminalPhysicalAllowanceCache.runWithCharges parsed seed rich :=
  BinaryResourceEmissionContinuation.cache_compat backend parsed seed rich

theorem cache_preceding (parsed : PhysicalRequest) (seed : BinarySeedLookupTree.Store) (rich : Bool) :
    BinaryResourceEmissionContinuation.preceding (cache parsed seed rich) = BinaryInitializerEmissionExecution.cache parsed seed rich :=
  BinaryResourceEmissionContinuation.cache_preceding backend parsed seed rich

def certified (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) :
    (((((Option (BinaryPRGHeapCertifiedPrefixLifetime.CachedResult
      parsed.1.2.logical.request rich) × FixedBinaryWord seed.width) × List Bool) × Trace) × ℕ) × BinaryExecutionCharges.Charges) × ((ℕ × ℕ) × ℕ) :=
  BinaryResourceEmissionContinuation.certified backend frame parsed hParsed seed rich

theorem certified_compat (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) :
    (certified frame parsed hParsed seed rich).1 = BinaryTerminalPhysicalAllowanceCertified.runWithCharges frame parsed hParsed seed rich :=
  BinaryResourceEmissionContinuation.certified_compat backend frame parsed hParsed seed rich

theorem certified_preceding (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) :
    BinaryResourceEmissionContinuation.preceding (certified frame parsed hParsed seed rich) = BinaryInitializerEmissionExecution.certified frame parsed hParsed seed rich :=
  BinaryResourceEmissionContinuation.certified_preceding backend frame parsed hParsed seed rich

def draw (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) :
    (((((BinaryPRGWordControllerTerminal.Result seed parsed.1.1 × List Bool) × Trace) × ℕ)) × BinaryExecutionCharges.Charges) × ((ℕ × ℕ) × ℕ) :=
  BinaryResourceEmissionContinuation.draw backend frame parsed hParsed seed rich K outer scalar

theorem draw_compat (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) :
    (draw frame parsed hParsed seed rich K outer scalar).1 = BinaryTerminalPhysicalCompleteDrawMeasured.runWithCharges frame parsed hParsed seed rich K outer scalar :=
  BinaryResourceEmissionContinuation.draw_compat backend frame parsed hParsed seed rich K outer scalar

theorem draw_preceding (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) :
    BinaryResourceEmissionContinuation.preceding (draw frame parsed hParsed seed rich K outer scalar) = BinaryInitializerEmissionExecution.draw frame parsed hParsed seed rich K outer scalar :=
  BinaryResourceEmissionContinuation.draw_preceding backend frame parsed hParsed seed rich K outer scalar

def fixed (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) :
    ((((((FixedArrayTable parsed.1.1 SignedWord × FixedBinaryWord seed.width) × List Bool) × Trace) × ℕ)) × BinaryExecutionCharges.Charges) × ((ℕ × ℕ) × ℕ) :=
  BinaryResourceEmissionContinuation.fixed backend frame parsed hParsed seed rich K outer scalar

theorem fixed_compat (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) :
    (fixed frame parsed hParsed seed rich K outer scalar).1 = BinaryTerminalPhysicalCompleteFixedMeasured.runWithCharges frame parsed hParsed seed rich K outer scalar :=
  BinaryResourceEmissionContinuation.fixed_compat backend frame parsed hParsed seed rich K outer scalar

theorem fixed_preceding (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) :
    BinaryResourceEmissionContinuation.preceding (fixed frame parsed hParsed seed rich K outer scalar) = BinaryInitializerEmissionExecution.fixed frame parsed hParsed seed rich K outer scalar :=
  BinaryResourceEmissionContinuation.fixed_preceding backend frame parsed hParsed seed rich K outer scalar

def framed (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (header : BinaryPRGHeaderFrame.Header parsed.1.1) :
    ((((((List Bool × FixedBinaryWord seed.width) × List Bool) × Trace) × ℕ)) × BinaryExecutionCharges.Charges) × ((ℕ × ℕ) × ℕ) :=
  BinaryResourceEmissionContinuation.framed backend frame parsed hParsed seed rich K outer scalar header

theorem framed_compat (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (header : BinaryPRGHeaderFrame.Header parsed.1.1) :
    (framed frame parsed hParsed seed rich K outer scalar header).1 = BinaryTerminalPhysicalCompleteFramedMeasured.runWithCharges frame parsed hParsed seed rich K outer scalar header :=
  BinaryResourceEmissionContinuation.framed_compat backend frame parsed hParsed seed rich K outer scalar header

theorem framed_preceding (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (header : BinaryPRGHeaderFrame.Header parsed.1.1) :
    BinaryResourceEmissionContinuation.preceding (framed frame parsed hParsed seed rich K outer scalar header) = BinaryInitializerEmissionExecution.framed frame parsed hParsed seed rich K outer scalar header :=
  BinaryResourceEmissionContinuation.framed_preceding backend frame parsed hParsed seed rich K outer scalar header

def seed (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (seed : List Bool) :
    ((((Option (List Bool) × List Bool) × Trace) × ℕ) × BinarySamplerExecutionCharges.Charges) × ((ℕ × ℕ) × ℕ) :=
  BinaryResourceEmissionContinuation.seed backend frame parsed hParsed rich seed

theorem seed_compat (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (bits : List Bool) :
    (seed frame parsed hParsed rich bits).1 = BinaryTerminalPhysicalCompleteSeedMeasured.runWithCharges frame parsed hParsed rich bits :=
  BinaryResourceEmissionContinuation.seed_compat backend frame parsed hParsed rich bits

theorem seed_preceding (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (bits : List Bool) :
    BinaryResourceEmissionContinuation.preceding (seed frame parsed hParsed rich bits) = BinaryInitializerEmissionExecution.seed frame parsed hParsed rich bits :=
  BinaryResourceEmissionContinuation.seed_preceding backend frame parsed hParsed rich bits

def raw (rich : Bool) (frame bits : List Bool) :
    ((((Option (List Bool) × List Bool) × Trace) × ℕ) × BinarySamplerExecutionCharges.Charges) × ((ℕ × ℕ) × ℕ) :=
  BinaryResourceEmissionContinuation.raw backend rich frame bits

theorem raw_compat (rich : Bool) (frame bits : List Bool) :
    (raw rich frame bits).1 = BinaryTerminalPhysicalCompleteRawMeasured.runWithCharges rich frame bits :=
  BinaryResourceEmissionContinuation.raw_compat backend rich frame bits

theorem raw_preceding (rich : Bool) (frame bits : List Bool) :
    BinaryResourceEmissionContinuation.preceding (raw rich frame bits) = BinaryInitializerEmissionExecution.raw rich frame bits :=
  BinaryResourceEmissionContinuation.raw_preceding backend rich frame bits

def parsedRaw (rich : Bool) (frame bits : List Bool) :
    ((((Option (List Bool) × List Bool) × Trace) × ℕ) × BinarySamplerExecutionCharges.Charges) × ((ℕ × ℕ) × ℕ) :=
  BinaryResourceEmissionContinuation.parsedRaw backend rich frame bits

theorem parsedRaw_compat (rich : Bool) (frame bits : List Bool) :
    (parsedRaw rich frame bits).1 = BinaryTerminalPhysicalParsedRawMeasured.runWithCharges rich frame bits :=
  BinaryResourceEmissionContinuation.parsedRaw_compat backend rich frame bits

theorem parsedRaw_preceding (rich : Bool) (frame bits : List Bool) :
    BinaryResourceEmissionContinuation.preceding (parsedRaw rich frame bits) = BinaryInitializerEmissionExecution.parsedRaw rich frame bits :=
  BinaryResourceEmissionContinuation.parsedRaw_preceding backend rich frame bits

def generated {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) :
    (((((Option (List Bool) × S) × List Bool) × Trace) × ℕ) × BinaryGenerationExecutionCharges.Charges) × ((ℕ × ℕ) × ℕ) :=
  BinaryResourceEmissionContinuation.generated backend next rich frame state

theorem generated_compat {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) :
    (generated next rich frame state).1 = BinaryTerminalPhysicalCompleteGeneratedMeasured.runWithGeneration next rich frame state :=
  BinaryResourceEmissionContinuation.generated_compat backend next rich frame state

theorem generated_preceding {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) :
    BinaryResourceEmissionContinuation.preceding (generated next rich frame state) = BinaryInitializerEmissionExecution.generated next rich frame state :=
  BinaryResourceEmissionContinuation.generated_preceding backend next rich frame state

def parsedGenerated {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) :
    (((((Option (List Bool) × S) × List Bool) × Trace) × ℕ) × BinaryGenerationExecutionCharges.Charges) × ((ℕ × ℕ) × ℕ) :=
  BinaryResourceEmissionContinuation.parsedGenerated backend next rich frame state

theorem parsedGenerated_compat {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) :
    (parsedGenerated next rich frame state).1 = BinaryTerminalPhysicalParsedGeneratedMeasured.runWithGeneration next rich frame state :=
  BinaryResourceEmissionContinuation.parsedGenerated_compat backend next rich frame state

theorem parsedGenerated_preceding {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) :
    BinaryResourceEmissionContinuation.preceding (parsedGenerated next rich frame state) = BinaryInitializerEmissionExecution.parsedGenerated next rich frame state :=
  BinaryResourceEmissionContinuation.parsedGenerated_preceding backend next rich frame state

def pair {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    ((((((Option (List Bool) × Option (List Bool)) × S) × (List Bool × List Bool)) × Trace) × ℕ) ×
      BinaryGenerationExecutionCharges.Charges) × ((ℕ × ℕ) × ℕ) :=
  BinaryResourceEmissionContinuation.pair backend next frame state

theorem pair_compat {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    (pair next frame state).1 = BinaryTerminalPhysicalCompleteGeneratedMeasured.pairWithGeneration next frame state :=
  BinaryResourceEmissionContinuation.pair_compat backend next frame state

theorem pair_preceding {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    BinaryResourceEmissionContinuation.preceding (pair next frame state) = BinaryInitializerEmissionExecution.pair next frame state :=
  BinaryResourceEmissionContinuation.pair_preceding backend next frame state

def parsedPair {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    ((((((Option (List Bool) × Option (List Bool)) × S) × (List Bool × List Bool)) × Trace) × ℕ) ×
      BinaryGenerationExecutionCharges.Charges) × ((ℕ × ℕ) × ℕ) :=
  BinaryResourceEmissionContinuation.parsedPair backend next frame state

theorem parsedPair_compat {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    (parsedPair next frame state).1 = BinaryTerminalPhysicalParsedGeneratedMeasured.pairWithGeneration next frame state :=
  BinaryResourceEmissionContinuation.parsedPair_compat backend next frame state

theorem parsedPair_preceding {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    BinaryResourceEmissionContinuation.preceding (parsedPair next frame state) = BinaryInitializerEmissionExecution.parsedPair next frame state :=
  BinaryResourceEmissionContinuation.parsedPair_preceding backend next frame state

end Blotto.BinaryCompleteInitialRequest
