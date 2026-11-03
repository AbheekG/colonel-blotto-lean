import Blotto.BinaryConstructionRequest
import Blotto.BinaryPrimitiveInitial
import Blotto.BinaryResourcePriceProjection

/-! A concrete resource backend retains every preceding price and adds actual
physical lookup source/emission work. The existing typed continuation is reused
with paired extras. Forgetting the new field gives the complete prior runner. -/
namespace Blotto.BinaryPrimitiveRequest
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryPRGPhysicalRawRequestLifetime (Request)
open BinaryTerminalPhysicalAllowanceCache (PhysicalRequest Parsed)
open BinaryPhysicalHeapAllowanceInitial (sourceAt_cap)
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable {n : ℕ}

def nativeAtWithEmission (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :=
  let selected := BinaryPRGResourceWork.resourceInput request.logical.request rich
  let primitive := BinaryPrimitiveInitial.sourceAtTraceWithWrites seed request rich pc hp
  let construction := primitive.1
  let entry := construction.1
  let supplied := entry.1
  let child := supplied.1
  let returned := child.1
  let produced := returned.1
  let drawn := produced.1.1
  match drawn.1.1.1.2.1 with
  | none =>
      let plan := BinaryTracePlanMeasured.Plan.join (.block [.frames 2,.arrayAllocation 16])
        (.shifted 2 drawn.1.2)
      let emitted := BinaryTracePlanMeasured.emitFull plan []
      ((((((((((((none,drawn.1.1.1.2.2),drawn.1.1.2),emitted.1.1),drawn.2+2),
        (produced.1.2,produced.2)),returned.2),emitted.1.2+emitted.2),child.2),supplied.2),entry.2),construction.2),primitive.2)
  | some state =>
      let terminal := BinaryHeapMaterializationPlan.materializeAt selected.length
        (BinaryPRGWordControllerBooleanResourceSource.capacityTable selected.length)
        drawn.1.1.1.1 (by simpa only [drawn,produced,returned,child,supplied,entry,construction,primitive,BinaryPrimitiveInitial.sourceAtTraceWithWrites_compat,
          BinaryConstructionInitial.sourceAtTraceWithWrites_compat,
          BinaryEnumerationInitial.sourceAtTraceWithWrites_compat,
          BinaryCompleteInitialEmission.sourceAtTraceWithWrites_compat,
          BinaryAllowanceEmissionInitial.sourceAtTraceWithWrites_compat,
          BinaryPhysicalHeapAllowanceInitial.sourceAt,BinaryPhysicalHeapAllowanceInitial.sourceAtMeasured,
          BinaryPhysicalHeapAllowanceInitial.sourceAtTraceMeasured]
          using sourceAt_cap seed request rich pc hp) state 2
      let plan := BinaryTracePlanMeasured.Plan.join (.block [.frames 2,.arrayAllocation 24])
        (.join (.shifted 2 drawn.1.2) terminal.1.2)
      let emitted := BinaryTracePlanMeasured.emitFull plan []
      ((((((((((((some terminal.1.1,drawn.1.1.1.2.2),drawn.1.1.2),
        emitted.1.1),drawn.2+terminal.2+4),
          (produced.1.2,produced.2)),returned.2),emitted.1.2+emitted.2),child.2),supplied.2),entry.2),construction.2),primitive.2)

theorem nativeAtWithEmission_compat (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (nativeAtWithEmission seed request rich pc hp).1 = BinaryConstructionRequest.nativeAtWithEmission seed request rich pc hp := by
  simp only [nativeAtWithEmission,BinaryConstructionRequest.nativeAtWithEmission,
    BinaryPrimitiveInitial.sourceAtTraceWithWrites_compat]
  split
  · rename_i hNone
    simp only [hNone]
  · rename_i state hSome
    simp only [hSome]

def runWithCharges (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool) :=
  let primitive := nativeAtWithEmission seed request rich (BinaryWordIndexCoinController.zeroIndex seed)
    (by rw [BinaryWordIndexCoinController.zeroIndex_value]; omega)
  let construction := primitive.1
  let entry := construction.1
  let supplied := entry.1
  let child := supplied.1
  let returned := child.1
  let drawn := returned.1.1.1
  let width := seed.cap.bits.length
  let plan := BinaryTracePlanMeasured.Plan.join
    (.block [.listAllocation width,.frames (width+2),.arrayAllocation 16,.frames 4,.arrayAllocation 24])
    (.shifted 4 drawn.1.2)
  let emitted := BinaryTracePlanMeasured.emitFull plan []
  ((((((((drawn.1.1,emitted.1.1),drawn.2+
      BinaryPhysicalNumericalReadbackLifetime.pairLookupAllowance request+
      BinaryPhysicalHeapRequestLifetime.preparationResidualAllowance request),
    (⟨returned.1.1.2.1,returned.1.1.2.2,returned.1.2,returned.2,emitted.1.2+emitted.2⟩ : BinaryExecutionCharges.Charges)),child.2),supplied.2),entry.2),construction.2),primitive.2)

theorem runWithCharges_compat (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool) :
    (runWithCharges seed request rich).1 = BinaryConstructionRequest.runWithCharges seed request rich := by
  simp only [runWithCharges,BinaryConstructionRequest.runWithCharges,nativeAtWithEmission_compat]

def backend : BinaryResourceEmissionContinuation.Backend (((ℕ × ℕ) × ℕ) × ℕ) where
  run := fun seed request rich =>
    let produced := runWithCharges seed request rich
    (produced.1.1.1.1,(((produced.1.1.1.2,produced.1.1.2),produced.1.2),produced.2))
  compat := by
    intro n seed request rich
    dsimp only
    rw [runWithCharges_compat,BinaryConstructionRequest.runWithCharges_compat,BinaryEnumerationRequest.runWithCharges_compat,BinaryCompleteInitialRequest.runWithCharges_compat]

theorem backend_refines : BinaryResourcePriceProjection.RunRefines backend BinaryConstructionRequest.backend := by
  intro n seed request rich
  dsimp only [backend,BinaryConstructionRequest.backend,BinaryResourcePriceProjection.keepRun]
  rw [runWithCharges_compat]

def cache (parsed : PhysicalRequest) (seed : BinarySeedLookupTree.Store) (rich : Bool) :
    (((((Option (BinaryPRGHeapCachedPrefixLifetime.CachedResult
      parsed.2.logical.request rich) × FixedBinaryWord seed.width) × List Bool) × Trace) × ℕ) ×
      BinaryExecutionCharges.Charges) × ((ℕ × ℕ) × (((ℕ × ℕ) × ℕ) × ℕ)) :=
  BinaryResourceEmissionContinuation.cache backend parsed seed rich

theorem cache_compat (parsed : PhysicalRequest) (seed : BinarySeedLookupTree.Store) (rich : Bool) :
    (cache parsed seed rich).1 = BinaryTerminalPhysicalAllowanceCache.runWithCharges parsed seed rich :=
  BinaryResourceEmissionContinuation.cache_compat backend parsed seed rich

theorem cache_preceding (parsed : PhysicalRequest) (seed : BinarySeedLookupTree.Store) (rich : Bool) :
    BinaryResourcePriceProjection.keepComplete (cache parsed seed rich) = BinaryConstructionRequest.cache parsed seed rich :=
  BinaryResourcePriceProjection.cache_keep backend BinaryConstructionRequest.backend backend_refines parsed seed rich

def certified (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) :
    (((((Option (BinaryPRGHeapCertifiedPrefixLifetime.CachedResult
      parsed.1.2.logical.request rich) × FixedBinaryWord seed.width) × List Bool) × Trace) × ℕ) × BinaryExecutionCharges.Charges) × ((ℕ × ℕ) × (((ℕ × ℕ) × ℕ) × ℕ)) :=
  BinaryResourceEmissionContinuation.certified backend frame parsed hParsed seed rich

theorem certified_compat (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) :
    (certified frame parsed hParsed seed rich).1 = BinaryTerminalPhysicalAllowanceCertified.runWithCharges frame parsed hParsed seed rich :=
  BinaryResourceEmissionContinuation.certified_compat backend frame parsed hParsed seed rich

theorem certified_preceding (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) :
    BinaryResourcePriceProjection.keepComplete (certified frame parsed hParsed seed rich) = BinaryConstructionRequest.certified frame parsed hParsed seed rich :=
  BinaryResourcePriceProjection.certified_keep backend BinaryConstructionRequest.backend backend_refines frame parsed hParsed seed rich

def draw (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) :
    (((((BinaryPRGWordControllerTerminal.Result seed parsed.1.1 × List Bool) × Trace) × ℕ)) × BinaryExecutionCharges.Charges) × ((ℕ × ℕ) × (((ℕ × ℕ) × ℕ) × ℕ)) :=
  BinaryResourceEmissionContinuation.draw backend frame parsed hParsed seed rich K outer scalar

theorem draw_compat (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) :
    (draw frame parsed hParsed seed rich K outer scalar).1 = BinaryTerminalPhysicalCompleteDrawMeasured.runWithCharges frame parsed hParsed seed rich K outer scalar :=
  BinaryResourceEmissionContinuation.draw_compat backend frame parsed hParsed seed rich K outer scalar

theorem draw_preceding (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) :
    BinaryResourcePriceProjection.keepComplete (draw frame parsed hParsed seed rich K outer scalar) = BinaryConstructionRequest.draw frame parsed hParsed seed rich K outer scalar :=
  BinaryResourcePriceProjection.draw_keep backend BinaryConstructionRequest.backend backend_refines frame parsed hParsed seed rich K outer scalar

def fixed (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) :
    ((((((FixedArrayTable parsed.1.1 SignedWord × FixedBinaryWord seed.width) × List Bool) × Trace) × ℕ)) × BinaryExecutionCharges.Charges) × ((ℕ × ℕ) × (((ℕ × ℕ) × ℕ) × ℕ)) :=
  BinaryResourceEmissionContinuation.fixed backend frame parsed hParsed seed rich K outer scalar

theorem fixed_compat (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) :
    (fixed frame parsed hParsed seed rich K outer scalar).1 = BinaryTerminalPhysicalCompleteFixedMeasured.runWithCharges frame parsed hParsed seed rich K outer scalar :=
  BinaryResourceEmissionContinuation.fixed_compat backend frame parsed hParsed seed rich K outer scalar

theorem fixed_preceding (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) :
    BinaryResourcePriceProjection.keepComplete (fixed frame parsed hParsed seed rich K outer scalar) = BinaryConstructionRequest.fixed frame parsed hParsed seed rich K outer scalar :=
  BinaryResourcePriceProjection.fixed_keep backend BinaryConstructionRequest.backend backend_refines frame parsed hParsed seed rich K outer scalar

def framed (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (header : BinaryPRGHeaderFrame.Header parsed.1.1) :
    ((((((List Bool × FixedBinaryWord seed.width) × List Bool) × Trace) × ℕ)) × BinaryExecutionCharges.Charges) × ((ℕ × ℕ) × (((ℕ × ℕ) × ℕ) × ℕ)) :=
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
    BinaryResourcePriceProjection.keepComplete (framed frame parsed hParsed seed rich K outer scalar header) = BinaryConstructionRequest.framed frame parsed hParsed seed rich K outer scalar header :=
  BinaryResourcePriceProjection.framed_keep backend BinaryConstructionRequest.backend backend_refines frame parsed hParsed seed rich K outer scalar header

def seed (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (seed : List Bool) :
    ((((Option (List Bool) × List Bool) × Trace) × ℕ) × BinarySamplerExecutionCharges.Charges) × ((ℕ × ℕ) × (((ℕ × ℕ) × ℕ) × ℕ)) :=
  BinaryResourceEmissionContinuation.seed backend frame parsed hParsed rich seed

theorem seed_compat (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (bits : List Bool) :
    (seed frame parsed hParsed rich bits).1 = BinaryTerminalPhysicalCompleteSeedMeasured.runWithCharges frame parsed hParsed rich bits :=
  BinaryResourceEmissionContinuation.seed_compat backend frame parsed hParsed rich bits

theorem seed_preceding (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (bits : List Bool) :
    BinaryResourcePriceProjection.keepComplete (seed frame parsed hParsed rich bits) = BinaryConstructionRequest.seed frame parsed hParsed rich bits :=
  BinaryResourcePriceProjection.seed_keep backend BinaryConstructionRequest.backend backend_refines frame parsed hParsed rich bits

def raw (rich : Bool) (frame bits : List Bool) :
    ((((Option (List Bool) × List Bool) × Trace) × ℕ) × BinarySamplerExecutionCharges.Charges) × ((ℕ × ℕ) × (((ℕ × ℕ) × ℕ) × ℕ)) :=
  BinaryResourceEmissionContinuation.raw backend rich frame bits

theorem raw_compat (rich : Bool) (frame bits : List Bool) :
    (raw rich frame bits).1 = BinaryTerminalPhysicalCompleteRawMeasured.runWithCharges rich frame bits :=
  BinaryResourceEmissionContinuation.raw_compat backend rich frame bits

theorem raw_preceding (rich : Bool) (frame bits : List Bool) :
    BinaryResourcePriceProjection.keepComplete (raw rich frame bits) = BinaryConstructionRequest.raw rich frame bits :=
  BinaryResourcePriceProjection.raw_keep backend BinaryConstructionRequest.backend backend_refines rich frame bits

def parsedRaw (rich : Bool) (frame bits : List Bool) :
    ((((Option (List Bool) × List Bool) × Trace) × ℕ) × BinarySamplerExecutionCharges.Charges) × ((ℕ × ℕ) × (((ℕ × ℕ) × ℕ) × ℕ)) :=
  BinaryResourceEmissionContinuation.parsedRaw backend rich frame bits

theorem parsedRaw_compat (rich : Bool) (frame bits : List Bool) :
    (parsedRaw rich frame bits).1 = BinaryTerminalPhysicalParsedRawMeasured.runWithCharges rich frame bits :=
  BinaryResourceEmissionContinuation.parsedRaw_compat backend rich frame bits

theorem parsedRaw_preceding (rich : Bool) (frame bits : List Bool) :
    BinaryResourcePriceProjection.keepComplete (parsedRaw rich frame bits) = BinaryConstructionRequest.parsedRaw rich frame bits :=
  BinaryResourcePriceProjection.parsedRaw_keep backend BinaryConstructionRequest.backend backend_refines rich frame bits

def generated {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) :
    (((((Option (List Bool) × S) × List Bool) × Trace) × ℕ) × BinaryGenerationExecutionCharges.Charges) × ((ℕ × ℕ) × (((ℕ × ℕ) × ℕ) × ℕ)) :=
  BinaryResourceEmissionContinuation.generated backend next rich frame state

theorem generated_compat {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) :
    (generated next rich frame state).1 = BinaryTerminalPhysicalCompleteGeneratedMeasured.runWithGeneration next rich frame state :=
  BinaryResourceEmissionContinuation.generated_compat backend next rich frame state

theorem generated_preceding {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) :
    BinaryResourcePriceProjection.keepComplete (generated next rich frame state) = BinaryConstructionRequest.generated next rich frame state :=
  BinaryResourcePriceProjection.generated_keep backend BinaryConstructionRequest.backend backend_refines next rich frame state

def parsedGenerated {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) :
    (((((Option (List Bool) × S) × List Bool) × Trace) × ℕ) × BinaryGenerationExecutionCharges.Charges) × ((ℕ × ℕ) × (((ℕ × ℕ) × ℕ) × ℕ)) :=
  BinaryResourceEmissionContinuation.parsedGenerated backend next rich frame state

theorem parsedGenerated_compat {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) :
    (parsedGenerated next rich frame state).1 = BinaryTerminalPhysicalParsedGeneratedMeasured.runWithGeneration next rich frame state :=
  BinaryResourceEmissionContinuation.parsedGenerated_compat backend next rich frame state

theorem parsedGenerated_preceding {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) :
    BinaryResourcePriceProjection.keepComplete (parsedGenerated next rich frame state) = BinaryConstructionRequest.parsedGenerated next rich frame state :=
  BinaryResourcePriceProjection.parsedGenerated_keep backend BinaryConstructionRequest.backend backend_refines next rich frame state

def pair {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    ((((((Option (List Bool) × Option (List Bool)) × S) × (List Bool × List Bool)) × Trace) × ℕ) ×
      BinaryGenerationExecutionCharges.Charges) × ((ℕ × ℕ) × (((ℕ × ℕ) × ℕ) × ℕ)) :=
  BinaryResourceEmissionContinuation.pair backend next frame state

theorem pair_compat {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    (pair next frame state).1 = BinaryTerminalPhysicalCompleteGeneratedMeasured.pairWithGeneration next frame state :=
  BinaryResourceEmissionContinuation.pair_compat backend next frame state

theorem pair_preceding {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    BinaryResourcePriceProjection.keepComplete (pair next frame state) = BinaryConstructionRequest.pair next frame state :=
  BinaryResourcePriceProjection.pair_keep backend BinaryConstructionRequest.backend backend_refines next frame state

def parsedPair {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    ((((((Option (List Bool) × Option (List Bool)) × S) × (List Bool × List Bool)) × Trace) × ℕ) ×
      BinaryGenerationExecutionCharges.Charges) × ((ℕ × ℕ) × (((ℕ × ℕ) × ℕ) × ℕ)) :=
  BinaryResourceEmissionContinuation.parsedPair backend next frame state

theorem parsedPair_compat {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    (parsedPair next frame state).1 = BinaryTerminalPhysicalParsedGeneratedMeasured.pairWithGeneration next frame state :=
  BinaryResourceEmissionContinuation.parsedPair_compat backend next frame state

theorem parsedPair_preceding {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    BinaryResourcePriceProjection.keepComplete (parsedPair next frame state) = BinaryConstructionRequest.parsedPair next frame state :=
  BinaryResourcePriceProjection.parsedPair_keep backend BinaryConstructionRequest.backend backend_refines next frame state

end Blotto.BinaryPrimitiveRequest
