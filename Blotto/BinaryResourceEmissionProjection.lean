import Blotto.BinaryResourceEmissionContinuation

/-! Forgetting a new typed resource price preserves the entire preceding
complete runner, including its previous additional price. The hypothesis is
full actual resource refinement and is discharged by concrete backends. -/
namespace Blotto.BinaryResourceEmissionProjection
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryTerminalPhysicalAllowanceCache (PhysicalRequest Parsed)
open BinaryResourceEmissionContinuation
set_option autoImplicit false
set_option maxHeartbeats 3000000

def keepRun {α E : Type*} (produced : α × (ℕ × E)) : α × ℕ := (produced.1,produced.2.1)

def keepComplete {α E : Type*} (produced : α × ((ℕ × ℕ) × (ℕ × E))) : α × ((ℕ × ℕ) × ℕ) :=
  (produced.1,(produced.2.1,produced.2.2.1))

def RunRefines {E : Type*} (backend : Backend (ℕ × E)) (prior : Backend ℕ) : Prop :=
  ∀ {n : ℕ} (seed : BinarySeedLookupTree.Store) (request : BinaryPRGPhysicalRawRequestLifetime.Request n) (rich : Bool),
    keepRun (backend.run seed request rich) = prior.run seed request rich

variable {E : Type*} [Zero E] [Add E]

theorem first_zero : (0 : ℕ × E).1 = 0 := rfl

theorem first_add (a b : ℕ × E) : (a+b).1 = a.1+b.1 := rfl

theorem cache_extra {F : Type*} (backend : Backend F) (parsed : PhysicalRequest) (seed : BinarySeedLookupTree.Store) (rich : Bool) :
    (cache backend parsed seed rich).2.2 = (backend.run seed parsed.2 rich).2 := by
  unfold cache
  dsimp only
  split <;> rfl

theorem cache_oldExtra (backend : Backend (ℕ × E)) (prior : Backend ℕ) (hRun : RunRefines backend prior) (parsed : PhysicalRequest) (seed : BinarySeedLookupTree.Store) (rich : Bool) :
    (cache backend parsed seed rich).2.2.1 = (cache prior parsed seed rich).2.2 := by
  rw [cache_extra,cache_extra]
  exact congrArg Prod.snd (hRun seed parsed.2 rich)

theorem certified_oldExtra (backend : Backend (ℕ × E)) (prior : Backend ℕ) (hRun : RunRefines backend prior) (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) :
    (certified backend frame parsed hParsed seed rich).2.2.1 = (certified prior frame parsed hParsed seed rich).2.2 := by
  exact cache_oldExtra backend prior hRun parsed.1 seed rich

theorem draw_oldExtra (backend : Backend (ℕ × E)) (prior : Backend ℕ) (hRun : RunRefines backend prior) (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) :
    (draw backend frame parsed hParsed seed rich K outer scalar).2.2.1 = (draw prior frame parsed hParsed seed rich K outer scalar).2.2 := by
  exact certified_oldExtra backend prior hRun frame parsed hParsed seed rich

theorem fixed_oldExtra (backend : Backend (ℕ × E)) (prior : Backend ℕ) (hRun : RunRefines backend prior) (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) :
    (fixed backend frame parsed hParsed seed rich K outer scalar).2.2.1 = (fixed prior frame parsed hParsed seed rich K outer scalar).2.2 := by
  exact draw_oldExtra backend prior hRun frame parsed hParsed seed rich K outer scalar

theorem framed_oldExtra (backend : Backend (ℕ × E)) (prior : Backend ℕ) (hRun : RunRefines backend prior) (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (header : BinaryPRGHeaderFrame.Header parsed.1.1) :
    (framed backend frame parsed hParsed seed rich K outer scalar header).2.2.1 = (framed prior frame parsed hParsed seed rich K outer scalar header).2.2 := by
  exact fixed_oldExtra backend prior hRun frame parsed hParsed seed rich K outer scalar

theorem seed_oldExtra (backend : Backend (ℕ × E)) (prior : Backend ℕ) (hRun : RunRefines backend prior) (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (bits : List Bool) :
    (seed backend frame parsed hParsed rich bits).2.2.1 = (seed prior frame parsed hParsed rich bits).2.2 := by
  unfold seed
  simp only [BinaryCacheContinuationCore.seed_record]
  unfold BinaryResourceEmissionContinuation.cacheBackend
  split
  · rename_i hNone
    simp only [hNone,first_zero]
  · rename_i held hSome
    simp only [hSome,framed_oldExtra backend prior hRun]

theorem raw_oldExtra (backend : Backend (ℕ × E)) (prior : Backend ℕ) (hRun : RunRefines backend prior) (rich : Bool) (frame bits : List Bool) :
    (raw backend rich frame bits).2.2.1 = (raw prior rich frame bits).2.2 := by
  unfold raw BinaryCacheContinuationCore.raw BinaryResourceEmissionContinuation.cacheBackend
  dsimp only
  split
  · simp only [first_zero]
  · split
    · simp only [seed_oldExtra backend prior hRun]
    · simp only [first_zero]

theorem parsedRaw_oldExtra (backend : Backend (ℕ × E)) (prior : Backend ℕ) (hRun : RunRefines backend prior) (rich : Bool) (frame bits : List Bool) :
    (parsedRaw backend rich frame bits).2.2.1 = (parsedRaw prior rich frame bits).2.2 := by
  unfold parsedRaw BinaryCacheContinuationCore.parsedRaw BinaryResourceEmissionContinuation.cacheBackend
  dsimp only
  split
  · simp only [first_zero]
  · split
    · simp only [seed_oldExtra backend prior hRun]
    · simp only [first_zero]

theorem generated_oldExtra (backend : Backend (ℕ × E)) (prior : Backend ℕ) (hRun : RunRefines backend prior) {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) :
    (generated backend next rich frame state).2.2.1 = (generated prior next rich frame state).2.2 := by
  unfold generated BinaryCacheContinuationCore.generated BinaryResourceEmissionContinuation.cacheBackend
  dsimp only
  split
  · simp only [first_zero]
  · split
    · simp only [seed_oldExtra backend prior hRun]
    · simp only [first_zero]

theorem parsedGenerated_oldExtra (backend : Backend (ℕ × E)) (prior : Backend ℕ) (hRun : RunRefines backend prior) {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) :
    (parsedGenerated backend next rich frame state).2.2.1 = (parsedGenerated prior next rich frame state).2.2 := by
  unfold parsedGenerated BinaryCacheContinuationCore.parsedGenerated BinaryResourceEmissionContinuation.cacheBackend
  dsimp only
  split
  · simp only [first_zero]
  · split
    · simp only [seed_oldExtra backend prior hRun]
    · simp only [first_zero]

theorem pair_oldExtra (backend : Backend (ℕ × E)) (prior : Backend ℕ) (hRun : RunRefines backend prior) {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    (pair backend next frame state).2.2.1 = (pair prior next frame state).2.2 := by
  simp only [pair,first_add,generated_oldExtra backend prior hRun,
    generated_compat backend,generated_compat prior,BinaryCacheContinuationCore.pair,BinaryResourceEmissionContinuation.cacheBackend]

theorem parsedPair_oldExtra (backend : Backend (ℕ × E)) (prior : Backend ℕ) (hRun : RunRefines backend prior) {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    (parsedPair backend next frame state).2.2.1 = (parsedPair prior next frame state).2.2 := by
  simp only [parsedPair,first_add,parsedGenerated_oldExtra backend prior hRun,
    parsedGenerated_compat backend,parsedGenerated_compat prior,BinaryCacheContinuationCore.parsedPair,BinaryResourceEmissionContinuation.cacheBackend]

theorem cache_keep (backend : Backend (ℕ × E)) (prior : Backend ℕ) (hRun : RunRefines backend prior) (parsed : PhysicalRequest) (seed : BinarySeedLookupTree.Store) (rich : Bool) :
    keepComplete (cache backend parsed seed rich) = cache prior parsed seed rich :=
  Prod.ext ((cache_compat backend parsed seed rich).trans (cache_compat prior parsed seed rich).symm)
    (Prod.ext ((cache_oldPrices backend parsed seed rich).trans (cache_oldPrices prior parsed seed rich).symm)
      (cache_oldExtra backend prior hRun parsed seed rich))

theorem certified_keep (backend : Backend (ℕ × E)) (prior : Backend ℕ) (hRun : RunRefines backend prior) (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) :
    keepComplete (certified backend frame parsed hParsed seed rich) = certified prior frame parsed hParsed seed rich :=
  Prod.ext ((certified_compat backend frame parsed hParsed seed rich).trans (certified_compat prior frame parsed hParsed seed rich).symm)
    (Prod.ext ((certified_oldPrices backend frame parsed hParsed seed rich).trans (certified_oldPrices prior frame parsed hParsed seed rich).symm)
      (certified_oldExtra backend prior hRun frame parsed hParsed seed rich))

theorem draw_keep (backend : Backend (ℕ × E)) (prior : Backend ℕ) (hRun : RunRefines backend prior) (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) :
    keepComplete (draw backend frame parsed hParsed seed rich K outer scalar) = draw prior frame parsed hParsed seed rich K outer scalar :=
  Prod.ext ((draw_compat backend frame parsed hParsed seed rich K outer scalar).trans (draw_compat prior frame parsed hParsed seed rich K outer scalar).symm)
    (Prod.ext ((draw_oldPrices backend frame parsed hParsed seed rich K outer scalar).trans (draw_oldPrices prior frame parsed hParsed seed rich K outer scalar).symm)
      (draw_oldExtra backend prior hRun frame parsed hParsed seed rich K outer scalar))

theorem fixed_keep (backend : Backend (ℕ × E)) (prior : Backend ℕ) (hRun : RunRefines backend prior) (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) :
    keepComplete (fixed backend frame parsed hParsed seed rich K outer scalar) = fixed prior frame parsed hParsed seed rich K outer scalar :=
  Prod.ext ((fixed_compat backend frame parsed hParsed seed rich K outer scalar).trans (fixed_compat prior frame parsed hParsed seed rich K outer scalar).symm)
    (Prod.ext ((fixed_oldPrices backend frame parsed hParsed seed rich K outer scalar).trans (fixed_oldPrices prior frame parsed hParsed seed rich K outer scalar).symm)
      (fixed_oldExtra backend prior hRun frame parsed hParsed seed rich K outer scalar))

theorem framed_keep (backend : Backend (ℕ × E)) (prior : Backend ℕ) (hRun : RunRefines backend prior) (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (header : BinaryPRGHeaderFrame.Header parsed.1.1) :
    keepComplete (framed backend frame parsed hParsed seed rich K outer scalar header) = framed prior frame parsed hParsed seed rich K outer scalar header :=
  Prod.ext ((framed_compat backend frame parsed hParsed seed rich K outer scalar header).trans (framed_compat prior frame parsed hParsed seed rich K outer scalar header).symm)
    (Prod.ext ((framed_oldPrices backend frame parsed hParsed seed rich K outer scalar header).trans (framed_oldPrices prior frame parsed hParsed seed rich K outer scalar header).symm)
      (framed_oldExtra backend prior hRun frame parsed hParsed seed rich K outer scalar header))

theorem seed_keep (backend : Backend (ℕ × E)) (prior : Backend ℕ) (hRun : RunRefines backend prior) (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (bits : List Bool) :
    keepComplete (seed backend frame parsed hParsed rich bits) = seed prior frame parsed hParsed rich bits :=
  Prod.ext ((seed_compat backend frame parsed hParsed rich bits).trans (seed_compat prior frame parsed hParsed rich bits).symm)
    (Prod.ext ((seed_oldPrices backend frame parsed hParsed rich bits).trans (seed_oldPrices prior frame parsed hParsed rich bits).symm)
      (seed_oldExtra backend prior hRun frame parsed hParsed rich bits))

theorem raw_keep (backend : Backend (ℕ × E)) (prior : Backend ℕ) (hRun : RunRefines backend prior) (rich : Bool) (frame bits : List Bool) :
    keepComplete (raw backend rich frame bits) = raw prior rich frame bits :=
  Prod.ext ((raw_compat backend rich frame bits).trans (raw_compat prior rich frame bits).symm)
    (Prod.ext ((raw_oldPrices backend rich frame bits).trans (raw_oldPrices prior rich frame bits).symm)
      (raw_oldExtra backend prior hRun rich frame bits))

theorem parsedRaw_keep (backend : Backend (ℕ × E)) (prior : Backend ℕ) (hRun : RunRefines backend prior) (rich : Bool) (frame bits : List Bool) :
    keepComplete (parsedRaw backend rich frame bits) = parsedRaw prior rich frame bits :=
  Prod.ext ((parsedRaw_compat backend rich frame bits).trans (parsedRaw_compat prior rich frame bits).symm)
    (Prod.ext ((parsedRaw_oldPrices backend rich frame bits).trans (parsedRaw_oldPrices prior rich frame bits).symm)
      (parsedRaw_oldExtra backend prior hRun rich frame bits))

theorem generated_keep (backend : Backend (ℕ × E)) (prior : Backend ℕ) (hRun : RunRefines backend prior) {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) :
    keepComplete (generated backend next rich frame state) = generated prior next rich frame state :=
  Prod.ext ((generated_compat backend next rich frame state).trans (generated_compat prior next rich frame state).symm)
    (Prod.ext ((generated_oldPrices backend next rich frame state).trans (generated_oldPrices prior next rich frame state).symm)
      (generated_oldExtra backend prior hRun next rich frame state))

theorem parsedGenerated_keep (backend : Backend (ℕ × E)) (prior : Backend ℕ) (hRun : RunRefines backend prior) {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) :
    keepComplete (parsedGenerated backend next rich frame state) = parsedGenerated prior next rich frame state :=
  Prod.ext ((parsedGenerated_compat backend next rich frame state).trans (parsedGenerated_compat prior next rich frame state).symm)
    (Prod.ext ((parsedGenerated_oldPrices backend next rich frame state).trans (parsedGenerated_oldPrices prior next rich frame state).symm)
      (parsedGenerated_oldExtra backend prior hRun next rich frame state))

theorem pair_keep (backend : Backend (ℕ × E)) (prior : Backend ℕ) (hRun : RunRefines backend prior) {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    keepComplete (pair backend next frame state) = pair prior next frame state :=
  Prod.ext ((pair_compat backend next frame state).trans (pair_compat prior next frame state).symm)
    (Prod.ext ((pair_oldPrices backend next frame state).trans (pair_oldPrices prior next frame state).symm)
      (pair_oldExtra backend prior hRun next frame state))

theorem parsedPair_keep (backend : Backend (ℕ × E)) (prior : Backend ℕ) (hRun : RunRefines backend prior) {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    keepComplete (parsedPair backend next frame state) = parsedPair prior next frame state :=
  Prod.ext ((parsedPair_compat backend next frame state).trans (parsedPair_compat prior next frame state).symm)
    (Prod.ext ((parsedPair_oldPrices backend next frame state).trans (parsedPair_oldPrices prior next frame state).symm)
      (parsedPair_oldExtra backend prior hRun next frame state))

end Blotto.BinaryResourceEmissionProjection
