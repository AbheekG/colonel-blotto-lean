import Blotto.BinaryCacheContinuationCore
import Blotto.BinaryPhysicalCachePlan
import Blotto.BinaryCacheEmissionBounds
import Blotto.BinaryInitializerEmissionBounds

/-! A complete continuation accepts an actual resource backend with a full
preceding-record refinement. Extra prices retain their own type and flow through
all reached children and sequential pairs. Concrete backends must be instantiated
and bounded before this is a complete execution theorem. -/
namespace Blotto.BinaryResourceEmissionContinuation
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryTerminalPhysicalAllowanceCache (PhysicalRequest Parsed)
open BinaryPRGResourceWork BinaryPRGTerminalWork BinaryCachedGroupInputHeight BinaryTerminalCacheCertificate
set_option autoImplicit false
set_option maxHeartbeats 3000000


abbrev ResourceRecord {n : ℕ} (seed : BinarySeedLookupTree.Store)
    (request : BinaryPRGPhysicalRawRequestLifetime.Request n) (rich : Bool) :=
  (((((BinaryPRGWordControllerResource.Result seed
    (BinaryPRGResourceWork.resourceInput request.logical.request rich).length × List Bool) × Trace) × ℕ) ×
    BinaryExecutionCharges.Charges) × ℕ)

structure Backend (E : Type*) where
  run : {n : ℕ} → (seed : BinarySeedLookupTree.Store) →
    (request : BinaryPRGPhysicalRawRequestLifetime.Request n) → (rich : Bool) → ResourceRecord seed request rich × E
  compat : ∀ {n : ℕ} (seed : BinarySeedLookupTree.Store)
    (request : BinaryPRGPhysicalRawRequestLifetime.Request n) (rich : Bool),
    (run seed request rich).1 = BinaryAllowanceEmissionRequest.runWithCharges seed request rich

variable {E : Type*} [Zero E] [Add E]

def cache (backend : Backend E) (parsed : PhysicalRequest) (seed : BinarySeedLookupTree.Store) (rich : Bool) :
    (((((Option (BinaryPRGHeapCachedPrefixLifetime.CachedResult
      parsed.2.logical.request rich) × FixedBinaryWord seed.width) × List Bool) × Trace) × ℕ) ×
      BinaryExecutionCharges.Charges) × ((ℕ × ℕ) × E) :=
  let supplied := backend.run seed parsed.2 rich
  let initialized := supplied.1
  let returned := initialized.1
  let resource := returned.1
  match resource.1.1.1.1 with
  | none =>
      let emitted := BinaryWrapperEmission.one 16 2 resource.1.2
      ((((((none,resource.1.1.1.2),resource.1.1.2),emitted.1),resource.2+4),
        BinaryExecutionCharges.addWrapper returned.2 emitted.2),((0,initialized.2),supplied.2))
  | some state =>
      let produced := BinaryPhysicalCachePlan.cacheWithEmission
        (terminalInput parsed.2.logical.request rich state) parsed.2.physical.lengthStore
      let cached := produced.1
      let emitted := BinaryWrapperEmission.two 24 2 resource.1.2 cached.1.2
      ((((((some ⟨state,cached.1.1⟩,resource.1.1.1.2),resource.1.1.2),emitted.1),resource.2+cached.2+8),
        BinaryExecutionCharges.addWrapper returned.2 emitted.2),((produced.2,initialized.2),supplied.2))

theorem cache_compat (backend : Backend E) (parsed : PhysicalRequest) (seed : BinarySeedLookupTree.Store) (rich : Bool) :
    (cache backend parsed seed rich).1 = BinaryTerminalPhysicalAllowanceCache.runWithCharges parsed seed rich := by
  unfold cache BinaryTerminalPhysicalAllowanceCache.runWithCharges
  dsimp only
  simp only [backend.compat,BinaryAllowanceEmissionRequest.runWithCharges_compat]
  split
  · rename_i hNone
    simp only [hNone,BinaryWrapperEmission.one]
  · rename_i state hSome
    simp only [hSome,BinaryPhysicalCachePlan.cacheWithEmission_compat,BinaryWrapperEmission.two]


@[reducible] def cacheBackend (backend : Backend E) : BinaryCacheContinuationCore.Backend E where
  run := cache backend
  compat := cache_compat backend

@[reducible] def certified (backend : Backend E) (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) :
    (((((Option (BinaryPRGHeapCertifiedPrefixLifetime.CachedResult
      parsed.1.2.logical.request rich) × FixedBinaryWord seed.width) × List Bool) × Trace) × ℕ) × BinaryExecutionCharges.Charges) × ((ℕ × ℕ) × E) :=
  BinaryCacheContinuationCore.certified (cacheBackend backend) frame parsed hParsed seed rich

theorem certified_compat (backend : Backend E) (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) :
    (certified backend frame parsed hParsed seed rich).1 = BinaryTerminalPhysicalAllowanceCertified.runWithCharges frame parsed hParsed seed rich :=
  BinaryCacheContinuationCore.certified_compat (cacheBackend backend) frame parsed hParsed seed rich

@[reducible] def draw (backend : Backend E) (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) :
    (((((BinaryPRGWordControllerTerminal.Result seed parsed.1.1 × List Bool) × Trace) × ℕ)) × BinaryExecutionCharges.Charges) × ((ℕ × ℕ) × E) :=
  BinaryCacheContinuationCore.draw (cacheBackend backend) frame parsed hParsed seed rich K outer scalar

theorem draw_compat (backend : Backend E) (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) :
    (draw backend frame parsed hParsed seed rich K outer scalar).1 = BinaryTerminalPhysicalCompleteDrawMeasured.runWithCharges frame parsed hParsed seed rich K outer scalar :=
  BinaryCacheContinuationCore.draw_compat (cacheBackend backend) frame parsed hParsed seed rich K outer scalar

@[reducible] def fixed (backend : Backend E) (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) :
    ((((((FixedArrayTable parsed.1.1 SignedWord × FixedBinaryWord seed.width) × List Bool) × Trace) × ℕ)) × BinaryExecutionCharges.Charges) × ((ℕ × ℕ) × E) :=
  BinaryCacheContinuationCore.fixed (cacheBackend backend) frame parsed hParsed seed rich K outer scalar

theorem fixed_compat (backend : Backend E) (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) :
    (fixed backend frame parsed hParsed seed rich K outer scalar).1 = BinaryTerminalPhysicalCompleteFixedMeasured.runWithCharges frame parsed hParsed seed rich K outer scalar :=
  BinaryCacheContinuationCore.fixed_compat (cacheBackend backend) frame parsed hParsed seed rich K outer scalar

@[reducible] def framed (backend : Backend E) (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (header : BinaryPRGHeaderFrame.Header parsed.1.1) :
    ((((((List Bool × FixedBinaryWord seed.width) × List Bool) × Trace) × ℕ)) × BinaryExecutionCharges.Charges) × ((ℕ × ℕ) × E) :=
  BinaryCacheContinuationCore.framed (cacheBackend backend) frame parsed hParsed seed rich K outer scalar header

theorem framed_compat (backend : Backend E) (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (header : BinaryPRGHeaderFrame.Header parsed.1.1) :
    (framed backend frame parsed hParsed seed rich K outer scalar header).1 = BinaryTerminalPhysicalCompleteFramedMeasured.runWithCharges frame parsed hParsed seed rich K outer scalar header :=
  BinaryCacheContinuationCore.framed_compat (cacheBackend backend) frame parsed hParsed seed rich K outer scalar header

@[reducible] def seed (backend : Backend E) (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (seed : List Bool) :
    ((((Option (List Bool) × List Bool) × Trace) × ℕ) × BinarySamplerExecutionCharges.Charges) × ((ℕ × ℕ) × E) :=
  BinaryCacheContinuationCore.seed (cacheBackend backend) frame parsed hParsed rich seed

theorem seed_compat (backend : Backend E) (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (bits : List Bool) :
    (seed backend frame parsed hParsed rich bits).1 = BinaryTerminalPhysicalCompleteSeedMeasured.runWithCharges frame parsed hParsed rich bits :=
  BinaryCacheContinuationCore.seed_compat (cacheBackend backend) frame parsed hParsed rich bits

@[reducible] def raw (backend : Backend E) (rich : Bool) (frame bits : List Bool) :
    ((((Option (List Bool) × List Bool) × Trace) × ℕ) × BinarySamplerExecutionCharges.Charges) × ((ℕ × ℕ) × E) :=
  BinaryCacheContinuationCore.raw (cacheBackend backend) rich frame bits

theorem raw_compat (backend : Backend E) (rich : Bool) (frame bits : List Bool) :
    (raw backend rich frame bits).1 = BinaryTerminalPhysicalCompleteRawMeasured.runWithCharges rich frame bits :=
  BinaryCacheContinuationCore.raw_compat (cacheBackend backend) rich frame bits

@[reducible] def parsedRaw (backend : Backend E) (rich : Bool) (frame bits : List Bool) :
    ((((Option (List Bool) × List Bool) × Trace) × ℕ) × BinarySamplerExecutionCharges.Charges) × ((ℕ × ℕ) × E) :=
  BinaryCacheContinuationCore.parsedRaw (cacheBackend backend) rich frame bits

theorem parsedRaw_compat (backend : Backend E) (rich : Bool) (frame bits : List Bool) :
    (parsedRaw backend rich frame bits).1 = BinaryTerminalPhysicalParsedRawMeasured.runWithCharges rich frame bits :=
  BinaryCacheContinuationCore.parsedRaw_compat (cacheBackend backend) rich frame bits

@[reducible] def generated (backend : Backend E) {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) :
    (((((Option (List Bool) × S) × List Bool) × Trace) × ℕ) × BinaryGenerationExecutionCharges.Charges) × ((ℕ × ℕ) × E) :=
  BinaryCacheContinuationCore.generated (cacheBackend backend) next rich frame state

theorem generated_compat (backend : Backend E) {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) :
    (generated backend next rich frame state).1 = BinaryTerminalPhysicalCompleteGeneratedMeasured.runWithGeneration next rich frame state :=
  BinaryCacheContinuationCore.generated_compat (cacheBackend backend) next rich frame state

@[reducible] def parsedGenerated (backend : Backend E) {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) :
    (((((Option (List Bool) × S) × List Bool) × Trace) × ℕ) × BinaryGenerationExecutionCharges.Charges) × ((ℕ × ℕ) × E) :=
  BinaryCacheContinuationCore.parsedGenerated (cacheBackend backend) next rich frame state

theorem parsedGenerated_compat (backend : Backend E) {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) :
    (parsedGenerated backend next rich frame state).1 = BinaryTerminalPhysicalParsedGeneratedMeasured.runWithGeneration next rich frame state :=
  BinaryCacheContinuationCore.parsedGenerated_compat (cacheBackend backend) next rich frame state

@[reducible] def pair (backend : Backend E) {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    ((((((Option (List Bool) × Option (List Bool)) × S) × (List Bool × List Bool)) × Trace) × ℕ) ×
      BinaryGenerationExecutionCharges.Charges) × ((ℕ × ℕ) × E) :=
  BinaryCacheContinuationCore.pair (cacheBackend backend) next frame state

theorem pair_compat (backend : Backend E) {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    (pair backend next frame state).1 = BinaryTerminalPhysicalCompleteGeneratedMeasured.pairWithGeneration next frame state :=
  BinaryCacheContinuationCore.pair_compat (cacheBackend backend) next frame state

@[reducible] def parsedPair (backend : Backend E) {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    ((((((Option (List Bool) × Option (List Bool)) × S) × (List Bool × List Bool)) × Trace) × ℕ) ×
      BinaryGenerationExecutionCharges.Charges) × ((ℕ × ℕ) × E) :=
  BinaryCacheContinuationCore.parsedPair (cacheBackend backend) next frame state

theorem parsedPair_compat (backend : Backend E) {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    (parsedPair backend next frame state).1 = BinaryTerminalPhysicalParsedGeneratedMeasured.pairWithGeneration next frame state :=
  BinaryCacheContinuationCore.parsedPair_compat (cacheBackend backend) next frame state

def preceding {α : Type*} (produced : α × ((ℕ × ℕ) × E)) : α × (ℕ × ℕ) := (produced.1,produced.2.1)

theorem cache_oldPrices (backend : Backend E) (parsed : PhysicalRequest) (seed : BinarySeedLookupTree.Store) (rich : Bool) :
    (cache backend parsed seed rich).2.1 = (BinaryInitializerEmissionExecution.cache parsed seed rich).2 := by
  unfold cache BinaryInitializerEmissionExecution.cache
  dsimp only
  simp only [backend.compat]
  split
  · rename_i hNone
    simp only [hNone]
  · rename_i state hSome
    simp only [hSome]

theorem certified_oldPrices (backend : Backend E) (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) :
    (certified backend frame parsed hParsed seed rich).2.1 = (BinaryInitializerEmissionExecution.certified frame parsed hParsed seed rich).2 :=
  BinaryCacheContinuationCore.certified_oldPrices (cacheBackend backend) (cache_oldPrices backend) frame parsed hParsed seed rich

theorem draw_oldPrices (backend : Backend E) (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) :
    (draw backend frame parsed hParsed seed rich K outer scalar).2.1 = (BinaryInitializerEmissionExecution.draw frame parsed hParsed seed rich K outer scalar).2 :=
  BinaryCacheContinuationCore.draw_oldPrices (cacheBackend backend) (cache_oldPrices backend) frame parsed hParsed seed rich K outer scalar

theorem fixed_oldPrices (backend : Backend E) (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) :
    (fixed backend frame parsed hParsed seed rich K outer scalar).2.1 = (BinaryInitializerEmissionExecution.fixed frame parsed hParsed seed rich K outer scalar).2 :=
  BinaryCacheContinuationCore.fixed_oldPrices (cacheBackend backend) (cache_oldPrices backend) frame parsed hParsed seed rich K outer scalar

theorem framed_oldPrices (backend : Backend E) (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (header : BinaryPRGHeaderFrame.Header parsed.1.1) :
    (framed backend frame parsed hParsed seed rich K outer scalar header).2.1 = (BinaryInitializerEmissionExecution.framed frame parsed hParsed seed rich K outer scalar header).2 :=
  BinaryCacheContinuationCore.framed_oldPrices (cacheBackend backend) (cache_oldPrices backend) frame parsed hParsed seed rich K outer scalar header

theorem seed_oldPrices (backend : Backend E) (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (bits : List Bool) :
    (seed backend frame parsed hParsed rich bits).2.1 = (BinaryInitializerEmissionExecution.seed frame parsed hParsed rich bits).2 :=
  BinaryCacheContinuationCore.seed_oldPrices (cacheBackend backend) (cache_oldPrices backend) frame parsed hParsed rich bits

theorem raw_oldPrices (backend : Backend E) (rich : Bool) (frame bits : List Bool) :
    (raw backend rich frame bits).2.1 = (BinaryInitializerEmissionExecution.raw rich frame bits).2 :=
  BinaryCacheContinuationCore.raw_oldPrices (cacheBackend backend) (cache_oldPrices backend) rich frame bits

theorem parsedRaw_oldPrices (backend : Backend E) (rich : Bool) (frame bits : List Bool) :
    (parsedRaw backend rich frame bits).2.1 = (BinaryInitializerEmissionExecution.parsedRaw rich frame bits).2 :=
  BinaryCacheContinuationCore.parsedRaw_oldPrices (cacheBackend backend) (cache_oldPrices backend) rich frame bits

theorem generated_oldPrices (backend : Backend E) {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) :
    (generated backend next rich frame state).2.1 = (BinaryInitializerEmissionExecution.generated next rich frame state).2 :=
  BinaryCacheContinuationCore.generated_oldPrices (cacheBackend backend) (cache_oldPrices backend) next rich frame state

theorem parsedGenerated_oldPrices (backend : Backend E) {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) :
    (parsedGenerated backend next rich frame state).2.1 = (BinaryInitializerEmissionExecution.parsedGenerated next rich frame state).2 :=
  BinaryCacheContinuationCore.parsedGenerated_oldPrices (cacheBackend backend) (cache_oldPrices backend) next rich frame state

theorem pair_oldPrices (backend : Backend E) {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    (pair backend next frame state).2.1 = (BinaryInitializerEmissionExecution.pair next frame state).2 :=
  BinaryCacheContinuationCore.pair_oldPrices (cacheBackend backend) (cache_oldPrices backend) next frame state

theorem parsedPair_oldPrices (backend : Backend E) {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    (parsedPair backend next frame state).2.1 = (BinaryInitializerEmissionExecution.parsedPair next frame state).2 :=
  BinaryCacheContinuationCore.parsedPair_oldPrices (cacheBackend backend) (cache_oldPrices backend) next frame state

theorem cache_preceding (backend : Backend E) (parsed : PhysicalRequest) (seed : BinarySeedLookupTree.Store) (rich : Bool) :
    preceding (cache backend parsed seed rich) = BinaryInitializerEmissionExecution.cache parsed seed rich :=
  Prod.ext ((cache_compat backend parsed seed rich).trans (BinaryInitializerEmissionExecution.cache_compat parsed seed rich).symm)
    (cache_oldPrices backend parsed seed rich)

theorem certified_preceding (backend : Backend E) (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) :
    preceding (certified backend frame parsed hParsed seed rich) = BinaryInitializerEmissionExecution.certified frame parsed hParsed seed rich :=
  Prod.ext ((certified_compat backend frame parsed hParsed seed rich).trans (BinaryInitializerEmissionExecution.certified_compat frame parsed hParsed seed rich).symm)
    (certified_oldPrices backend frame parsed hParsed seed rich)

theorem draw_preceding (backend : Backend E) (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) :
    preceding (draw backend frame parsed hParsed seed rich K outer scalar) = BinaryInitializerEmissionExecution.draw frame parsed hParsed seed rich K outer scalar :=
  Prod.ext ((draw_compat backend frame parsed hParsed seed rich K outer scalar).trans (BinaryInitializerEmissionExecution.draw_compat frame parsed hParsed seed rich K outer scalar).symm)
    (draw_oldPrices backend frame parsed hParsed seed rich K outer scalar)

theorem fixed_preceding (backend : Backend E) (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) :
    preceding (fixed backend frame parsed hParsed seed rich K outer scalar) = BinaryInitializerEmissionExecution.fixed frame parsed hParsed seed rich K outer scalar :=
  Prod.ext ((fixed_compat backend frame parsed hParsed seed rich K outer scalar).trans (BinaryInitializerEmissionExecution.fixed_compat frame parsed hParsed seed rich K outer scalar).symm)
    (fixed_oldPrices backend frame parsed hParsed seed rich K outer scalar)

theorem framed_preceding (backend : Backend E) (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (header : BinaryPRGHeaderFrame.Header parsed.1.1) :
    preceding (framed backend frame parsed hParsed seed rich K outer scalar header) = BinaryInitializerEmissionExecution.framed frame parsed hParsed seed rich K outer scalar header :=
  Prod.ext ((framed_compat backend frame parsed hParsed seed rich K outer scalar header).trans (BinaryInitializerEmissionExecution.framed_compat frame parsed hParsed seed rich K outer scalar header).symm)
    (framed_oldPrices backend frame parsed hParsed seed rich K outer scalar header)

theorem seed_preceding (backend : Backend E) (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (bits : List Bool) :
    preceding (seed backend frame parsed hParsed rich bits) = BinaryInitializerEmissionExecution.seed frame parsed hParsed rich bits :=
  Prod.ext ((seed_compat backend frame parsed hParsed rich bits).trans (BinaryInitializerEmissionExecution.seed_compat frame parsed hParsed rich bits).symm)
    (seed_oldPrices backend frame parsed hParsed rich bits)

theorem raw_preceding (backend : Backend E) (rich : Bool) (frame bits : List Bool) :
    preceding (raw backend rich frame bits) = BinaryInitializerEmissionExecution.raw rich frame bits :=
  Prod.ext ((raw_compat backend rich frame bits).trans (BinaryInitializerEmissionExecution.raw_compat rich frame bits).symm)
    (raw_oldPrices backend rich frame bits)

theorem parsedRaw_preceding (backend : Backend E) (rich : Bool) (frame bits : List Bool) :
    preceding (parsedRaw backend rich frame bits) = BinaryInitializerEmissionExecution.parsedRaw rich frame bits :=
  Prod.ext ((parsedRaw_compat backend rich frame bits).trans (BinaryInitializerEmissionExecution.parsedRaw_compat rich frame bits).symm)
    (parsedRaw_oldPrices backend rich frame bits)

theorem generated_preceding (backend : Backend E) {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) :
    preceding (generated backend next rich frame state) = BinaryInitializerEmissionExecution.generated next rich frame state :=
  Prod.ext ((generated_compat backend next rich frame state).trans (BinaryInitializerEmissionExecution.generated_compat next rich frame state).symm)
    (generated_oldPrices backend next rich frame state)

theorem parsedGenerated_preceding (backend : Backend E) {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) :
    preceding (parsedGenerated backend next rich frame state) = BinaryInitializerEmissionExecution.parsedGenerated next rich frame state :=
  Prod.ext ((parsedGenerated_compat backend next rich frame state).trans (BinaryInitializerEmissionExecution.parsedGenerated_compat next rich frame state).symm)
    (parsedGenerated_oldPrices backend next rich frame state)

theorem pair_preceding (backend : Backend E) {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    preceding (pair backend next frame state) = BinaryInitializerEmissionExecution.pair next frame state :=
  Prod.ext ((pair_compat backend next frame state).trans (BinaryInitializerEmissionExecution.pair_compat next frame state).symm)
    (pair_oldPrices backend next frame state)

theorem parsedPair_preceding (backend : Backend E) {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    preceding (parsedPair backend next frame state) = BinaryInitializerEmissionExecution.parsedPair next frame state :=
  Prod.ext ((parsedPair_compat backend next frame state).trans (BinaryInitializerEmissionExecution.parsedPair_compat next frame state).symm)
    (parsedPair_oldPrices backend next frame state)

end Blotto.BinaryResourceEmissionContinuation
