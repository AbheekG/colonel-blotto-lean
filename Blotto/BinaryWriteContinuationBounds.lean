import Blotto.BinaryWriteContinuationRequest
import Blotto.BinaryPackedContinuationBounds

/-! Reached persistent-write raw reader/allocator leaf emissions are bounded
by their actual retained trace and carried through the complete sampler.
Preceding counters remain exact. Native and physical-space joins stay separate. -/
namespace Blotto.BinaryWriteContinuationBounds
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryWriteContinuationRequest BinaryPRGTerminalWork
open BinaryTerminalPhysicalAllowanceCache (PhysicalRequest Parsed)
open BinaryPRGPhysicalRawRequestLifetime (Request)
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable {n : ℕ}
attribute [local irreducible] BinaryWriteContinuationRequest.seed

local macro "normalize_cache_aliases" : tactic =>
  `(tactic| try dsimp only [BinaryResourceEmissionContinuation.certified,
    BinaryResourceEmissionContinuation.draw,
    BinaryResourceEmissionContinuation.fixed,
    BinaryResourceEmissionContinuation.framed,
    BinaryResourceEmissionContinuation.seed,
    BinaryResourceEmissionContinuation.raw,
    BinaryResourceEmissionContinuation.parsedRaw,
    BinaryResourceEmissionContinuation.generated,
    BinaryResourceEmissionContinuation.parsedGenerated,
    BinaryResourceEmissionContinuation.pair,
    BinaryResourceEmissionContinuation.parsedPair,
    BinaryResourceEmissionContinuation.cacheBackend,
    BinaryWriteContinuationRequest.cache,
    BinaryWriteContinuationRequest.certified,
    BinaryWriteContinuationRequest.draw,
    BinaryWriteContinuationRequest.fixed,
    BinaryWriteContinuationRequest.framed,
    BinaryWriteContinuationRequest.seed,
    BinaryWriteContinuationRequest.raw,
    BinaryWriteContinuationRequest.parsedRaw,
    BinaryWriteContinuationRequest.generated,
    BinaryWriteContinuationRequest.parsedGenerated,
    BinaryWriteContinuationRequest.pair,
    BinaryWriteContinuationRequest.parsedPair] at *)

theorem plan_bound (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) (depth : ℕ) :
    let produced := BinaryWriteContinuationInitial.sourcePlanWithWritesAt seed request rich pc hp depth
    produced.2 ≤ 25*BinaryTracePlanMeasured.payload produced.1.1.1.1.1.1.1.1.1.1.1.2 := by
  unfold BinaryWriteContinuationInitial.sourcePlanWithWritesAt
  dsimp only
  refine (BinaryWriteLoopBackend.run_price _ _ _ _ _ _ _).trans ?_
  simp only [BinaryTracePlanMeasured.payload,List.length_cons,List.length_nil]
  (normalize_cache_aliases; all_goals omega)

theorem source_bound (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    let produced := BinaryWriteContinuationInitial.sourceAtTraceWithWrites seed request rich pc hp
    produced.2 ≤ 25*produced.1.1.1.1.1.1.1.1.1.1.1.2.length := by
  have h := plan_bound seed request rich pc hp 0
  simpa only [BinaryWriteContinuationInitial.sourceAtTraceWithWrites,BinaryTracePlanMeasured.emitFull_erases,
    BinaryTracePlanMeasured.emit_length,List.length_nil,Nat.add_zero] using h

theorem native_bound (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    let produced := nativeAtWithEmission seed request rich pc hp
    produced.2 ≤ 25*produced.1.1.1.1.1.1.1.1.1.1.1.2.length := by
  have h := source_bound seed request rich pc hp
  dsimp only at h
  unfold nativeAtWithEmission
  dsimp only
  split <;> simp only [BinaryTracePlanMeasured.emitFull_erases,BinaryTracePlanMeasured.emit_length,
    BinaryTracePlanMeasured.payload,List.length_cons,List.length_nil,Nat.add_zero] <;> (normalize_cache_aliases; all_goals omega)

theorem run_bound (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool) :
    let produced := runWithCharges seed request rich
    produced.2 ≤ 25*produced.1.1.1.1.1.1.1.1.1.2.length := by
  have h := native_bound seed request rich (BinaryWordIndexCoinController.zeroIndex seed)
    (by rw [BinaryWordIndexCoinController.zeroIndex_value]; (normalize_cache_aliases; all_goals omega))
  dsimp only at h
  simp only [runWithCharges,BinaryTracePlanMeasured.emitFull_erases,BinaryTracePlanMeasured.emit_length,
    BinaryTracePlanMeasured.payload,List.length_cons,List.length_nil,Nat.add_zero]
  (normalize_cache_aliases; all_goals omega)

theorem cache_relative (parsed : PhysicalRequest) (seed : BinarySeedLookupTree.Store) (rich : Bool) :
    (cache parsed seed rich).2.2.2 ≤ 25*(cache parsed seed rich).1.1.1.2.length := by
  have h := run_bound seed parsed.2 rich
  unfold cache BinaryResourceEmissionContinuation.cache
  dsimp only [backend]
  split <;> simp only [BinaryWrapperEmission.one_length,BinaryWrapperEmission.two_length] <;> (normalize_cache_aliases; all_goals omega)

theorem certified_relative (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) :
    (certified frame parsed hParsed seed rich).2.2.2 ≤ 25*(certified frame parsed hParsed seed rich).1.1.1.2.length := by
  have he := cache_relative parsed.1 seed rich
  unfold certified BinaryResourceEmissionContinuation.certified BinaryCacheContinuationCore.certified BinaryResourceEmissionContinuation.cacheBackend
  dsimp only
  split <;> simp only [BinaryWrapperEmission.one_length,BinaryWrapperEmission.two_length,
    BinaryWriteContinuationRequest.cache] at he ⊢ <;> (normalize_cache_aliases; all_goals omega)

theorem draw_relative (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) :
    (draw frame parsed hParsed seed rich K outer scalar).2.2.2 ≤
      25*(draw frame parsed hParsed seed rich K outer scalar).1.1.1.2.length := by
  have he := certified_relative frame parsed hParsed seed rich
  simp only [draw,BinaryResourceEmissionContinuation.draw,BinaryCacheContinuationCore.draw_record,BinaryResourceEmissionContinuation.cacheBackend]
  split <;> simp only [BinaryWrapperEmission.one_length,BinaryWrapperEmission.two_length,
    BinaryWriteContinuationRequest.certified] at he ⊢ <;> (normalize_cache_aliases; all_goals omega)

theorem fixed_relative (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) :
    (fixed frame parsed hParsed seed rich K outer scalar).2.2.2 ≤
      25*(fixed frame parsed hParsed seed rich K outer scalar).1.1.1.2.length := by
  have he := draw_relative frame parsed hParsed seed rich K outer scalar
  simp only [fixed,BinaryResourceEmissionContinuation.fixed,BinaryCacheContinuationCore.fixed_record,BinaryResourceEmissionContinuation.cacheBackend]
  split <;> simp only [BinaryWrapperEmission.one_length,BinaryWrapperEmission.two_length,
    BinaryWriteContinuationRequest.draw] at he ⊢ <;> (normalize_cache_aliases; all_goals omega)

theorem framed_relative (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (header : BinaryPRGHeaderFrame.Header parsed.1.1) :
    (framed frame parsed hParsed seed rich K outer scalar header).2.2.2 ≤
      25*(framed frame parsed hParsed seed rich K outer scalar header).1.1.1.2.length := by
  have he := fixed_relative frame parsed hParsed seed rich K outer scalar
  simp only [framed,BinaryResourceEmissionContinuation.framed,BinaryWrapperEmission.listTwo_length,
    BinaryWriteContinuationRequest.fixed,BinaryCacheContinuationCore.framed_record,BinaryResourceEmissionContinuation.cacheBackend] at he ⊢
  (normalize_cache_aliases; all_goals omega)

theorem seed_relative (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (bits : List Bool) :
    (BinaryWriteContinuationRequest.seed frame parsed hParsed rich bits).2.2.2 ≤
      25*(BinaryWriteContinuationRequest.seed frame parsed hParsed rich bits).1.1.1.2.length := by
  unfold BinaryWriteContinuationRequest.seed BinaryResourceEmissionContinuation.seed
  simp only [BinaryCacheContinuationCore.seed_record]
  unfold BinaryResourceEmissionContinuation.cacheBackend
  split
  · exact Nat.zero_le _
  · rename_i held hSome
    have he := framed_relative frame parsed hParsed held.2.1 rich parsed.1.2.logical.request.precision
      held.1.outer held.1.scalar parsed.1.2.logical.header
    simp only [BinarySeedWrapperEmission.nested_length,BinaryWriteContinuationRequest.framed] at he ⊢
    (normalize_cache_aliases; all_goals omega)

theorem uniform_seed : ∃ C d : ℕ,∀ (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed) (rich : Bool) (bits : List Bool),
    (BinaryWriteContinuationRequest.seed frame parsed hParsed rich bits).2.2.2 ≤ C*(frame.length+1)^d := by
  obtain ⟨T,t,hTrace⟩ := BinaryCompleteSeedEventBounds.accepted_trace
  refine ⟨25*T,t,?_⟩
  intro frame parsed hParsed rich bits
  have he := seed_relative frame parsed hParsed rich bits
  rw [seed_compat] at he
  have ht := hTrace frame parsed hParsed rich bits
  change (BinaryTerminalPhysicalCompleteSeedMeasured.runWithCharges frame parsed hParsed rich bits).1.1.2.length ≤ _ at ht
  nlinarith only [he,ht]

theorem raw_uniform : ∃ C d : ℕ,∀ (rich : Bool) (frame bits : List Bool),
    (raw rich frame bits).2.2.2 ≤ C*(frame.length+1)^d := by
  obtain ⟨C,d,hSeed⟩ := uniform_seed
  refine ⟨C,d,?_⟩
  intro rich frame bits
  unfold raw BinaryResourceEmissionContinuation.raw BinaryCacheContinuationCore.raw BinaryResourceEmissionContinuation.cacheBackend
  dsimp only
  split
  · exact Nat.zero_le _
  · rename_i parsed hRead
    split
    · simpa only [BinaryWriteContinuationRequest.seed] using hSeed frame parsed hRead rich bits
    · exact Nat.zero_le _

theorem parsedRaw_uniform : ∃ C d : ℕ,∀ (rich : Bool) (frame bits : List Bool),
    (parsedRaw rich frame bits).2.2.2 ≤ C*(frame.length+1)^d := by
  obtain ⟨C,d,hSeed⟩ := uniform_seed
  refine ⟨C,d,?_⟩
  intro rich frame bits
  unfold parsedRaw BinaryResourceEmissionContinuation.parsedRaw BinaryCacheContinuationCore.parsedRaw BinaryResourceEmissionContinuation.cacheBackend
  dsimp only
  split
  · exact Nat.zero_le _
  · rename_i parsed hRead
    split
    · simpa only [BinaryWriteContinuationRequest.seed] using hSeed frame parsed ((congrArg Prod.fst (BinaryPRGPhysicalRawRequestMeasured.read_erases frame)).symm.trans hRead) rich bits
    · exact Nat.zero_le _

theorem generated_uniform : ∃ C d : ℕ,∀ {S : Type*} (next : S → Bool × S) (rich : Bool) (frame : List Bool) (state : S),
    (generated next rich frame state).2.2.2 ≤ C*(frame.length+1)^d := by
  obtain ⟨C,d,hSeed⟩ := uniform_seed
  refine ⟨C,d,?_⟩
  intro S next rich frame state
  unfold generated BinaryResourceEmissionContinuation.generated BinaryCacheContinuationCore.generated BinaryResourceEmissionContinuation.cacheBackend
  dsimp only
  split
  · exact Nat.zero_le _
  · rename_i parsed hRead
    split
    · simpa only [BinaryWriteContinuationRequest.seed] using hSeed frame parsed hRead rich
        (BinaryFreshGenerationPlan.generateWithEmission next parsed.1.2.logical state).1.1.1.1
    · exact Nat.zero_le _

theorem parsedGenerated_uniform : ∃ C d : ℕ,∀ {S : Type*} (next : S → Bool × S) (rich : Bool) (frame : List Bool) (state : S),
    (parsedGenerated next rich frame state).2.2.2 ≤ C*(frame.length+1)^d := by
  obtain ⟨C,d,hSeed⟩ := uniform_seed
  refine ⟨C,d,?_⟩
  intro S next rich frame state
  unfold parsedGenerated BinaryResourceEmissionContinuation.parsedGenerated BinaryCacheContinuationCore.parsedGenerated BinaryResourceEmissionContinuation.cacheBackend
  dsimp only
  split
  · exact Nat.zero_le _
  · rename_i parsed hRead
    split
    · simpa only [BinaryWriteContinuationRequest.seed] using hSeed frame parsed ((congrArg Prod.fst (BinaryPRGPhysicalRawRequestMeasured.read_erases frame)).symm.trans hRead) rich
        (BinaryFreshGenerationPlan.generateWithEmission next parsed.1.2.logical state).1.1.1.1
    · exact Nat.zero_le _

theorem pair_uniform : ∃ C d : ℕ,∀ {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S),
    (pair next frame state).2.2.2 ≤ C*(frame.length+1)^d := by
  obtain ⟨C,d,hSingle⟩ := generated_uniform
  refine ⟨2*C,d,?_⟩
  intro S next frame state
  have hr := hSingle next true frame state
  have hp := hSingle next false frame (generated next true frame state).1.1.1.1.1.2
  change (generated next true frame state).2.2.2+
    (generated next false frame (generated next true frame state).1.1.1.1.1.2).2.2.2 ≤ _
  nlinarith only [hr,hp]

theorem parsedPair_uniform : ∃ C d : ℕ,∀ {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S),
    (parsedPair next frame state).2.2.2 ≤ C*(frame.length+1)^d := by
  obtain ⟨C,d,hSingle⟩ := parsedGenerated_uniform
  refine ⟨2*C,d,?_⟩
  intro S next frame state
  have hr := hSingle next true frame state
  have hp := hSingle next false frame (parsedGenerated next true frame state).1.1.1.1.1.2
  change (parsedGenerated next true frame state).2.2.2+
    (parsedGenerated next false frame (parsedGenerated next true frame state).1.1.1.1.1.2).2.2.2 ≤ _
  nlinarith only [hr,hp]

theorem raw_joint : ∃ C d : ℕ,∀ (rich : Bool) (frame bits : List Bool),
    let produced := raw rich frame bits
    produced.1.1.2+BinaryBigEndian.littleValue produced.1.1.1.1.2+usage produced.1.1.1.2+
      BinarySamplerExecutionCharges.total produced.1.2+produced.2.1.1+produced.2.1.2+produced.2.2.1.1.1.1.1+produced.2.2.1.1.1.1.2+produced.2.2.1.1.1.2+produced.2.2.1.1.2+produced.2.2.1.2+produced.2.2.2 ≤ C*(frame.length+1)^d := by
  obtain ⟨C,d,hOld⟩ := BinaryPackedContinuationBounds.raw_joint
  obtain ⟨P,e,hEmission⟩ := raw_uniform
  refine ⟨C+P,max d e,?_⟩
  intro rich frame bits
  have ho := hOld rich frame bits
  dsimp only at ho
  simp only [← raw_preceding,BinaryResourcePriceProjection.keepComplete] at ho
  have he := hEmission rich frame bits
  have hX : 0 < frame.length+1 := by (normalize_cache_aliases; all_goals omega)
  have hd := Nat.mul_le_mul_left C (Nat.pow_le_pow_right hX (Nat.le_max_left d e))
  have hp := Nat.mul_le_mul_left P (Nat.pow_le_pow_right hX (Nat.le_max_right d e))
  dsimp only
  nlinarith only [ho,he,hd,hp]

theorem parsedRaw_joint : ∃ C d : ℕ,∀ (rich : Bool) (frame bits : List Bool),
    let produced := parsedRaw rich frame bits
    produced.1.1.2+BinaryBigEndian.littleValue produced.1.1.1.1.2+usage produced.1.1.1.2+
      BinarySamplerExecutionCharges.total produced.1.2+produced.2.1.1+produced.2.1.2+produced.2.2.1.1.1.1.1+produced.2.2.1.1.1.1.2+produced.2.2.1.1.1.2+produced.2.2.1.1.2+produced.2.2.1.2+produced.2.2.2 ≤ C*(frame.length+1)^d := by
  obtain ⟨C,d,hOld⟩ := BinaryPackedContinuationBounds.parsedRaw_joint
  obtain ⟨P,e,hEmission⟩ := parsedRaw_uniform
  refine ⟨C+P,max d e,?_⟩
  intro rich frame bits
  have ho := hOld rich frame bits
  dsimp only at ho
  simp only [← parsedRaw_preceding,BinaryResourcePriceProjection.keepComplete] at ho
  have he := hEmission rich frame bits
  have hX : 0 < frame.length+1 := by (normalize_cache_aliases; all_goals omega)
  have hd := Nat.mul_le_mul_left C (Nat.pow_le_pow_right hX (Nat.le_max_left d e))
  have hp := Nat.mul_le_mul_left P (Nat.pow_le_pow_right hX (Nat.le_max_right d e))
  dsimp only
  nlinarith only [ho,he,hd,hp]

theorem generated_joint : ∃ C d : ℕ,∀ {S : Type*} (next : S → Bool × S) (rich : Bool) (frame : List Bool) (state : S),
    let produced := generated next rich frame state
    produced.1.1.2+BinaryBigEndian.littleValue produced.1.1.1.1.2+usage produced.1.1.1.2+
      BinaryGenerationExecutionCharges.total produced.1.2+produced.2.1.1+produced.2.1.2+produced.2.2.1.1.1.1.1+produced.2.2.1.1.1.1.2+produced.2.2.1.1.1.2+produced.2.2.1.1.2+produced.2.2.1.2+produced.2.2.2 ≤ C*(frame.length+1)^d := by
  obtain ⟨C,d,hOld⟩ := BinaryPackedContinuationBounds.generated_joint
  obtain ⟨P,e,hEmission⟩ := generated_uniform
  refine ⟨C+P,max d e,?_⟩
  intro S next rich frame state
  have ho := hOld next rich frame state
  dsimp only at ho
  simp only [← generated_preceding,BinaryResourcePriceProjection.keepComplete] at ho
  have he := hEmission next rich frame state
  have hX : 0 < frame.length+1 := by (normalize_cache_aliases; all_goals omega)
  have hd := Nat.mul_le_mul_left C (Nat.pow_le_pow_right hX (Nat.le_max_left d e))
  have hp := Nat.mul_le_mul_left P (Nat.pow_le_pow_right hX (Nat.le_max_right d e))
  dsimp only
  nlinarith only [ho,he,hd,hp]

theorem parsedGenerated_joint : ∃ C d : ℕ,∀ {S : Type*} (next : S → Bool × S) (rich : Bool) (frame : List Bool) (state : S),
    let produced := parsedGenerated next rich frame state
    produced.1.1.2+BinaryBigEndian.littleValue produced.1.1.1.1.2+usage produced.1.1.1.2+
      BinaryGenerationExecutionCharges.total produced.1.2+produced.2.1.1+produced.2.1.2+produced.2.2.1.1.1.1.1+produced.2.2.1.1.1.1.2+produced.2.2.1.1.1.2+produced.2.2.1.1.2+produced.2.2.1.2+produced.2.2.2 ≤ C*(frame.length+1)^d := by
  obtain ⟨C,d,hOld⟩ := BinaryPackedContinuationBounds.parsedGenerated_joint
  obtain ⟨P,e,hEmission⟩ := parsedGenerated_uniform
  refine ⟨C+P,max d e,?_⟩
  intro S next rich frame state
  have ho := hOld next rich frame state
  dsimp only at ho
  simp only [← parsedGenerated_preceding,BinaryResourcePriceProjection.keepComplete] at ho
  have he := hEmission next rich frame state
  have hX : 0 < frame.length+1 := by (normalize_cache_aliases; all_goals omega)
  have hd := Nat.mul_le_mul_left C (Nat.pow_le_pow_right hX (Nat.le_max_left d e))
  have hp := Nat.mul_le_mul_left P (Nat.pow_le_pow_right hX (Nat.le_max_right d e))
  dsimp only
  nlinarith only [ho,he,hd,hp]

theorem pair_joint : ∃ C d : ℕ,∀ {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S),
    let produced := pair next frame state
    produced.1.1.2+BinaryBigEndian.littleValue produced.1.1.1.1.2.1+BinaryBigEndian.littleValue produced.1.1.1.1.2.2+usage produced.1.1.1.2+
      BinaryGenerationExecutionCharges.total produced.1.2+produced.2.1.1+produced.2.1.2+produced.2.2.1.1.1.1.1+produced.2.2.1.1.1.1.2+produced.2.2.1.1.1.2+produced.2.2.1.1.2+produced.2.2.1.2+produced.2.2.2 ≤ C*(frame.length+1)^d := by
  obtain ⟨C,d,hOld⟩ := BinaryPackedContinuationBounds.pair_joint
  obtain ⟨P,e,hEmission⟩ := pair_uniform
  refine ⟨C+P,max d e,?_⟩
  intro S next frame state
  have ho := hOld next frame state
  dsimp only at ho
  simp only [← pair_preceding,BinaryResourcePriceProjection.keepComplete] at ho
  have he := hEmission next frame state
  have hX : 0 < frame.length+1 := by (normalize_cache_aliases; all_goals omega)
  have hd := Nat.mul_le_mul_left C (Nat.pow_le_pow_right hX (Nat.le_max_left d e))
  have hp := Nat.mul_le_mul_left P (Nat.pow_le_pow_right hX (Nat.le_max_right d e))
  dsimp only
  nlinarith only [ho,he,hd,hp]

theorem parsedPair_joint : ∃ C d : ℕ,∀ {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S),
    let produced := parsedPair next frame state
    produced.1.1.2+BinaryBigEndian.littleValue produced.1.1.1.1.2.1+BinaryBigEndian.littleValue produced.1.1.1.1.2.2+usage produced.1.1.1.2+
      BinaryGenerationExecutionCharges.total produced.1.2+produced.2.1.1+produced.2.1.2+produced.2.2.1.1.1.1.1+produced.2.2.1.1.1.1.2+produced.2.2.1.1.1.2+produced.2.2.1.1.2+produced.2.2.1.2+produced.2.2.2 ≤ C*(frame.length+1)^d := by
  obtain ⟨C,d,hOld⟩ := BinaryPackedContinuationBounds.parsedPair_joint
  obtain ⟨P,e,hEmission⟩ := parsedPair_uniform
  refine ⟨C+P,max d e,?_⟩
  intro S next frame state
  have ho := hOld next frame state
  dsimp only at ho
  simp only [← parsedPair_preceding,BinaryResourcePriceProjection.keepComplete] at ho
  have he := hEmission next frame state
  have hX : 0 < frame.length+1 := by (normalize_cache_aliases; all_goals omega)
  have hd := Nat.mul_le_mul_left C (Nat.pow_le_pow_right hX (Nat.le_max_left d e))
  have hp := Nat.mul_le_mul_left P (Nat.pow_le_pow_right hX (Nat.le_max_right d e))
  dsimp only
  nlinarith only [ho,he,hd,hp]

theorem counter_width (source allowance retained : ℕ) (prior : BinaryGenerationExecutionCharges.Charges)
    (cacheEmission calculatorEmission additionalEmission enumerationPrice constructionPrice primitivePrice continuationPrice writePrice L C d : ℕ)
    (hBound : source+allowance+retained+BinaryGenerationExecutionCharges.total prior+
      cacheEmission+calculatorEmission+additionalEmission+enumerationPrice+constructionPrice+primitivePrice+continuationPrice+writePrice ≤ C*(L+1)^d) :
    ∀ counter ∈ [source,prior.sampler.execution.primitive,prior.sampler.execution.coinSource,prior.sampler.execution.write,
      prior.sampler.execution.native,prior.sampler.execution.wrappers,prior.sampler.seedEmission,prior.generationEmission,
      cacheEmission,calculatorEmission,additionalEmission,enumerationPrice,constructionPrice,primitivePrice,continuationPrice,writePrice],
      binaryWordWidth counter ≤ binaryWordWidth C+1+d*binaryWordWidth (L+1) := by
  have hf := BinaryGenerationExecutionCharges.fields_le_total prior
  have hm := binaryWordWidth_mul C ((L+1)^d)
  have hp := Farey.binaryWordWidth_power (L+1) d
  have hWidth := binaryWordWidth_mono hBound
  intro counter hCounter
  have hc : counter ≤ source+allowance+retained+BinaryGenerationExecutionCharges.total prior+
      cacheEmission+calculatorEmission+additionalEmission+enumerationPrice+constructionPrice+primitivePrice+continuationPrice+writePrice := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hCounter
    rcases hCounter with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst counter <;> (normalize_cache_aliases; all_goals omega)
  have hw := binaryWordWidth_mono hc
  (normalize_cache_aliases; all_goals omega)

theorem parsedGenerated_scalar_width : ∃ C d : ℕ,∀ {S : Type*} (next : S → Bool × S) (rich : Bool) (frame : List Bool) (state : S),
    let produced := parsedGenerated next rich frame state
    ∀ counter ∈ [produced.1.1.2,produced.1.2.sampler.execution.primitive,produced.1.2.sampler.execution.coinSource,
      produced.1.2.sampler.execution.write,produced.1.2.sampler.execution.native,produced.1.2.sampler.execution.wrappers,
      produced.1.2.sampler.seedEmission,produced.1.2.generationEmission,produced.2.1.1,produced.2.1.2,produced.2.2.1.1.1.1.1,produced.2.2.1.1.1.1.2,produced.2.2.1.1.1.2,produced.2.2.1.1.2,produced.2.2.1.2,produced.2.2.2],
      binaryWordWidth counter ≤ binaryWordWidth C+1+d*binaryWordWidth (frame.length+1) := by
  obtain ⟨C,d,hBound⟩ := parsedGenerated_joint
  exact ⟨C,d,fun next rich frame state => counter_width _ _ _ _ _ _ _ _ _ _ _ _ _ C d (hBound next rich frame state)⟩

theorem parsedPair_scalar_width : ∃ C d : ℕ,∀ {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S),
    let produced := parsedPair next frame state
    ∀ counter ∈ [produced.1.1.2,produced.1.2.sampler.execution.primitive,produced.1.2.sampler.execution.coinSource,
      produced.1.2.sampler.execution.write,produced.1.2.sampler.execution.native,produced.1.2.sampler.execution.wrappers,
      produced.1.2.sampler.seedEmission,produced.1.2.generationEmission,produced.2.1.1,produced.2.1.2,produced.2.2.1.1.1.1.1,produced.2.2.1.1.1.1.2,produced.2.2.1.1.1.2,produced.2.2.1.1.2,produced.2.2.1.2,produced.2.2.2],
      binaryWordWidth counter ≤ binaryWordWidth C+1+d*binaryWordWidth (frame.length+1) := by
  obtain ⟨C,d,hBound⟩ := parsedPair_joint
  refine ⟨C,d,?_⟩
  intro S next frame state
  exact counter_width _ (_+_) _ _ _ _ _ _ _ _ _ _ _ C d (by simpa only [Nat.add_assoc] using hBound next frame state)


end Blotto.BinaryWriteContinuationBounds
