import Blotto.BinaryWriteContinuationRequest
import Blotto.BinaryObjectCachePlan
import Blotto.BinaryCacheContinuationProjection

/-! The concrete complete cache consumes planned object getters once and
forwards their reached emissions. All prior prices and complete results are
preserved through the shared post-cache continuation, with no replay. -/
namespace Blotto.BinaryObjectCacheRequest
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryTerminalPhysicalAllowanceCache (PhysicalRequest Parsed)
open BinaryPRGTerminalWork
set_option autoImplicit false
set_option maxHeartbeats 3000000

abbrev Prices := (((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ)

def prior : BinaryCacheContinuationCore.Backend Prices :=
  BinaryResourceEmissionContinuation.cacheBackend BinaryWriteContinuationRequest.backend

def cache (parsed : PhysicalRequest) (seed : BinarySeedLookupTree.Store) (rich : Bool) :
    (((((Option (BinaryPRGHeapCachedPrefixLifetime.CachedResult
      parsed.2.logical.request rich) × FixedBinaryWord seed.width) × List Bool) × Trace) × ℕ) ×
      BinaryExecutionCharges.Charges) × ((ℕ × ℕ) × (Prices × ℕ)) :=
  let supplied := BinaryWriteContinuationRequest.backend.run seed parsed.2 rich
  let initialized := supplied.1
  let returned := initialized.1
  let resource := returned.1
  match resource.1.1.1.1 with
  | none =>
      let emitted := BinaryWrapperEmission.one 16 2 resource.1.2
      ((((((none,resource.1.1.1.2),resource.1.1.2),emitted.1),resource.2+4),
        BinaryExecutionCharges.addWrapper returned.2 emitted.2),((0,initialized.2),(supplied.2,0)))
  | some state =>
      let getterCache := BinaryObjectCachePlan.cacheWithEmission
        (terminalInput parsed.2.logical.request rich state) parsed.2.physical.lengthStore
      let produced := getterCache.1
      let cached := produced.1
      let emitted := BinaryWrapperEmission.two 24 2 resource.1.2 cached.1.2
      ((((((some ⟨state,cached.1.1⟩,resource.1.1.1.2),resource.1.1.2),emitted.1),resource.2+cached.2+8),
        BinaryExecutionCharges.addWrapper returned.2 emitted.2),((produced.2,initialized.2),(supplied.2,getterCache.2)))

theorem cache_preceding (parsed : PhysicalRequest) (seed : BinarySeedLookupTree.Store) (rich : Bool) :
    BinaryCacheContinuationProjection.keepComplete (cache parsed seed rich) = BinaryWriteContinuationRequest.cache parsed seed rich := by
  simp only [cache,BinaryWriteContinuationRequest.cache,BinaryResourceEmissionContinuation.cache,
    BinaryCacheContinuationProjection.keepComplete]
  split
  · rename_i hNone
    simp only [hNone]
  · rename_i state hSome
    simp only [hSome,BinaryObjectCachePlan.cache_compat]

theorem cache_compat (parsed : PhysicalRequest) (seed : BinarySeedLookupTree.Store) (rich : Bool) :
    (cache parsed seed rich).1 = BinaryTerminalPhysicalAllowanceCache.runWithCharges parsed seed rich :=
  (congrArg Prod.fst (cache_preceding parsed seed rich)).trans (BinaryWriteContinuationRequest.cache_compat parsed seed rich)

def backend : BinaryCacheContinuationCore.Backend (Prices × ℕ) where
  run := cache
  compat := cache_compat

theorem backend_refines : BinaryCacheContinuationProjection.RunRefines backend prior := by
  intro parsed seed rich
  exact cache_preceding parsed seed rich

theorem prior_prices : BinaryCacheContinuationCore.OldPrices prior :=
  BinaryResourceEmissionContinuation.cache_oldPrices BinaryWriteContinuationRequest.backend

def certified (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) :
    (((((Option (BinaryPRGHeapCertifiedPrefixLifetime.CachedResult
      parsed.1.2.logical.request rich) × FixedBinaryWord seed.width) × List Bool) × Trace) × ℕ) × BinaryExecutionCharges.Charges) × ((ℕ × ℕ) × (Prices × ℕ)) :=
  BinaryCacheContinuationCore.certified backend frame parsed hParsed seed rich

theorem certified_compat (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) :
    (certified frame parsed hParsed seed rich).1 = BinaryTerminalPhysicalAllowanceCertified.runWithCharges frame parsed hParsed seed rich :=
  BinaryCacheContinuationCore.certified_compat backend frame parsed hParsed seed rich

theorem certified_preceding (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) :
    BinaryCacheContinuationProjection.keepComplete (certified frame parsed hParsed seed rich) = BinaryWriteContinuationRequest.certified frame parsed hParsed seed rich :=
  BinaryCacheContinuationProjection.certified_keep backend prior backend_refines prior_prices frame parsed hParsed seed rich

def draw (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) :
    (((((BinaryPRGWordControllerTerminal.Result seed parsed.1.1 × List Bool) × Trace) × ℕ)) × BinaryExecutionCharges.Charges) × ((ℕ × ℕ) × (Prices × ℕ)) :=
  BinaryCacheContinuationCore.draw backend frame parsed hParsed seed rich K outer scalar

theorem draw_compat (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) :
    (draw frame parsed hParsed seed rich K outer scalar).1 = BinaryTerminalPhysicalCompleteDrawMeasured.runWithCharges frame parsed hParsed seed rich K outer scalar :=
  BinaryCacheContinuationCore.draw_compat backend frame parsed hParsed seed rich K outer scalar

theorem draw_preceding (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) :
    BinaryCacheContinuationProjection.keepComplete (draw frame parsed hParsed seed rich K outer scalar) = BinaryWriteContinuationRequest.draw frame parsed hParsed seed rich K outer scalar :=
  BinaryCacheContinuationProjection.draw_keep backend prior backend_refines prior_prices frame parsed hParsed seed rich K outer scalar

def fixed (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) :
    ((((((FixedArrayTable parsed.1.1 SignedWord × FixedBinaryWord seed.width) × List Bool) × Trace) × ℕ)) × BinaryExecutionCharges.Charges) × ((ℕ × ℕ) × (Prices × ℕ)) :=
  BinaryCacheContinuationCore.fixed backend frame parsed hParsed seed rich K outer scalar

theorem fixed_compat (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) :
    (fixed frame parsed hParsed seed rich K outer scalar).1 = BinaryTerminalPhysicalCompleteFixedMeasured.runWithCharges frame parsed hParsed seed rich K outer scalar :=
  BinaryCacheContinuationCore.fixed_compat backend frame parsed hParsed seed rich K outer scalar

theorem fixed_preceding (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) :
    BinaryCacheContinuationProjection.keepComplete (fixed frame parsed hParsed seed rich K outer scalar) = BinaryWriteContinuationRequest.fixed frame parsed hParsed seed rich K outer scalar :=
  BinaryCacheContinuationProjection.fixed_keep backend prior backend_refines prior_prices frame parsed hParsed seed rich K outer scalar

def framed (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (header : BinaryPRGHeaderFrame.Header parsed.1.1) :
    ((((((List Bool × FixedBinaryWord seed.width) × List Bool) × Trace) × ℕ)) × BinaryExecutionCharges.Charges) × ((ℕ × ℕ) × (Prices × ℕ)) :=
  BinaryCacheContinuationCore.framed backend frame parsed hParsed seed rich K outer scalar header

theorem framed_compat (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (header : BinaryPRGHeaderFrame.Header parsed.1.1) :
    (framed frame parsed hParsed seed rich K outer scalar header).1 = BinaryTerminalPhysicalCompleteFramedMeasured.runWithCharges frame parsed hParsed seed rich K outer scalar header :=
  BinaryCacheContinuationCore.framed_compat backend frame parsed hParsed seed rich K outer scalar header

theorem framed_preceding (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (header : BinaryPRGHeaderFrame.Header parsed.1.1) :
    BinaryCacheContinuationProjection.keepComplete (framed frame parsed hParsed seed rich K outer scalar header) = BinaryWriteContinuationRequest.framed frame parsed hParsed seed rich K outer scalar header :=
  BinaryCacheContinuationProjection.framed_keep backend prior backend_refines prior_prices frame parsed hParsed seed rich K outer scalar header

def seed (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (seed : List Bool) :
    ((((Option (List Bool) × List Bool) × Trace) × ℕ) × BinarySamplerExecutionCharges.Charges) × ((ℕ × ℕ) × (Prices × ℕ)) :=
  BinaryCacheContinuationCore.seed backend frame parsed hParsed rich seed

theorem seed_compat (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (bits : List Bool) :
    (seed frame parsed hParsed rich bits).1 = BinaryTerminalPhysicalCompleteSeedMeasured.runWithCharges frame parsed hParsed rich bits :=
  BinaryCacheContinuationCore.seed_compat backend frame parsed hParsed rich bits

theorem seed_preceding (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (bits : List Bool) :
    BinaryCacheContinuationProjection.keepComplete (seed frame parsed hParsed rich bits) = BinaryWriteContinuationRequest.seed frame parsed hParsed rich bits :=
  BinaryCacheContinuationProjection.seed_keep backend prior backend_refines prior_prices frame parsed hParsed rich bits

def raw (rich : Bool) (frame bits : List Bool) :
    ((((Option (List Bool) × List Bool) × Trace) × ℕ) × BinarySamplerExecutionCharges.Charges) × ((ℕ × ℕ) × (Prices × ℕ)) :=
  BinaryCacheContinuationCore.raw backend rich frame bits

theorem raw_compat (rich : Bool) (frame bits : List Bool) :
    (raw rich frame bits).1 = BinaryTerminalPhysicalCompleteRawMeasured.runWithCharges rich frame bits :=
  BinaryCacheContinuationCore.raw_compat backend rich frame bits

theorem raw_preceding (rich : Bool) (frame bits : List Bool) :
    BinaryCacheContinuationProjection.keepComplete (raw rich frame bits) = BinaryWriteContinuationRequest.raw rich frame bits :=
  BinaryCacheContinuationProjection.raw_keep backend prior backend_refines prior_prices rich frame bits

def parsedRaw (rich : Bool) (frame bits : List Bool) :
    ((((Option (List Bool) × List Bool) × Trace) × ℕ) × BinarySamplerExecutionCharges.Charges) × ((ℕ × ℕ) × (Prices × ℕ)) :=
  BinaryCacheContinuationCore.parsedRaw backend rich frame bits

theorem parsedRaw_compat (rich : Bool) (frame bits : List Bool) :
    (parsedRaw rich frame bits).1 = BinaryTerminalPhysicalParsedRawMeasured.runWithCharges rich frame bits :=
  BinaryCacheContinuationCore.parsedRaw_compat backend rich frame bits

theorem parsedRaw_preceding (rich : Bool) (frame bits : List Bool) :
    BinaryCacheContinuationProjection.keepComplete (parsedRaw rich frame bits) = BinaryWriteContinuationRequest.parsedRaw rich frame bits :=
  BinaryCacheContinuationProjection.parsedRaw_keep backend prior backend_refines prior_prices rich frame bits

def generated {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) :
    (((((Option (List Bool) × S) × List Bool) × Trace) × ℕ) × BinaryGenerationExecutionCharges.Charges) × ((ℕ × ℕ) × (Prices × ℕ)) :=
  BinaryCacheContinuationCore.generated backend next rich frame state

theorem generated_compat {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) :
    (generated next rich frame state).1 = BinaryTerminalPhysicalCompleteGeneratedMeasured.runWithGeneration next rich frame state :=
  BinaryCacheContinuationCore.generated_compat backend next rich frame state

theorem generated_preceding {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) :
    BinaryCacheContinuationProjection.keepComplete (generated next rich frame state) = BinaryWriteContinuationRequest.generated next rich frame state :=
  BinaryCacheContinuationProjection.generated_keep backend prior backend_refines prior_prices next rich frame state

def parsedGenerated {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) :
    (((((Option (List Bool) × S) × List Bool) × Trace) × ℕ) × BinaryGenerationExecutionCharges.Charges) × ((ℕ × ℕ) × (Prices × ℕ)) :=
  BinaryCacheContinuationCore.parsedGenerated backend next rich frame state

theorem parsedGenerated_compat {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) :
    (parsedGenerated next rich frame state).1 = BinaryTerminalPhysicalParsedGeneratedMeasured.runWithGeneration next rich frame state :=
  BinaryCacheContinuationCore.parsedGenerated_compat backend next rich frame state

theorem parsedGenerated_preceding {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) :
    BinaryCacheContinuationProjection.keepComplete (parsedGenerated next rich frame state) = BinaryWriteContinuationRequest.parsedGenerated next rich frame state :=
  BinaryCacheContinuationProjection.parsedGenerated_keep backend prior backend_refines prior_prices next rich frame state

def pair {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    ((((((Option (List Bool) × Option (List Bool)) × S) × (List Bool × List Bool)) × Trace) × ℕ) ×
      BinaryGenerationExecutionCharges.Charges) × ((ℕ × ℕ) × (Prices × ℕ)) :=
  BinaryCacheContinuationCore.pair backend next frame state

theorem pair_compat {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    (pair next frame state).1 = BinaryTerminalPhysicalCompleteGeneratedMeasured.pairWithGeneration next frame state :=
  BinaryCacheContinuationCore.pair_compat backend next frame state

theorem pair_preceding {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    BinaryCacheContinuationProjection.keepComplete (pair next frame state) = BinaryWriteContinuationRequest.pair next frame state :=
  BinaryCacheContinuationProjection.pair_keep backend prior backend_refines prior_prices next frame state

def parsedPair {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    ((((((Option (List Bool) × Option (List Bool)) × S) × (List Bool × List Bool)) × Trace) × ℕ) ×
      BinaryGenerationExecutionCharges.Charges) × ((ℕ × ℕ) × (Prices × ℕ)) :=
  BinaryCacheContinuationCore.parsedPair backend next frame state

theorem parsedPair_compat {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    (parsedPair next frame state).1 = BinaryTerminalPhysicalParsedGeneratedMeasured.pairWithGeneration next frame state :=
  BinaryCacheContinuationCore.parsedPair_compat backend next frame state

theorem parsedPair_preceding {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    BinaryCacheContinuationProjection.keepComplete (parsedPair next frame state) = BinaryWriteContinuationRequest.parsedPair next frame state :=
  BinaryCacheContinuationProjection.parsedPair_keep backend prior backend_refines prior_prices next frame state

end Blotto.BinaryObjectCacheRequest
