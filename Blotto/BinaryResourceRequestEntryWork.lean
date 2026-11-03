import Blotto.BinaryResourceArithmeticEntryWork
import Blotto.BinaryParserArithmeticEntryWork
import Blotto.BinaryPromiseOpcodeBounds

/-! The reached preparation/resource/cache entry class survives complete request
wrappers and the actual sequential draw order. Terminal draw/fallback/output
arithmetic and the full native/space interpretation remain separate classes. -/
namespace Blotto.BinaryResourceRequestEntryWork
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryTracePlanMeasured
open BinaryTerminalPhysicalAllowanceCache (Parsed)
set_option autoImplicit false
set_option maxHeartbeats 5000000

theorem certified_bound (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) :
    BinaryResourceArithmeticEntryWork.cache parsed.1 seed rich ≤
      2*listCells (BinaryCacheFinishRequest.certified frame parsed hParsed seed rich).1.1.1.2 := by
  have h := BinaryResourceArithmeticEntryWork.cache_bound parsed.1 seed rich
  simp only [BinaryCacheFinishRequest.certified,BinaryCacheContinuationCore.certified,BinaryCacheFinishRequest.backend]
  split <;> simp only [BinaryWrapperEmission.one_trace,BinaryWrapperEmission.two_trace,
    wrap,combine,listCells_append,listCells_under,listCells] <;> omega

theorem draw_bound (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) :
    BinaryResourceArithmeticEntryWork.cache parsed.1 seed rich ≤
      2*listCells (BinaryCacheFinishRequest.draw frame parsed hParsed seed rich K outer scalar).1.1.1.2 := by
  have h := certified_bound frame parsed hParsed seed rich
  dsimp only [BinaryCacheFinishRequest.certified] at h
  simp only [BinaryCacheFinishRequest.draw,BinaryCacheContinuationCore.draw_record]
  split <;> simp only [BinaryWrapperEmission.one_trace,BinaryWrapperEmission.two_trace,
    wrap,combine,listCells_append,listCells_under,listCells] <;> omega

theorem fixed_bound (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) :
    BinaryResourceArithmeticEntryWork.cache parsed.1 seed rich ≤
      2*listCells (BinaryCacheFinishRequest.fixed frame parsed hParsed seed rich K outer scalar).1.1.1.2 := by
  have h := draw_bound frame parsed hParsed seed rich K outer scalar
  dsimp only [BinaryCacheFinishRequest.draw] at h
  simp only [BinaryCacheFinishRequest.fixed,BinaryCacheContinuationCore.fixed_record]
  split <;> simp only [BinaryWrapperEmission.one_trace,BinaryWrapperEmission.two_trace,
    wrap,combine,listCells_append,listCells_under,listCells] <;> omega

theorem framed_bound (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (header : BinaryPRGHeaderFrame.Header parsed.1.1) :
    BinaryResourceArithmeticEntryWork.cache parsed.1 seed rich ≤
      2*listCells (BinaryCacheFinishRequest.framed frame parsed hParsed seed rich K outer scalar header).1.1.1.2 := by
  have h := fixed_bound frame parsed hParsed seed rich K outer scalar
  dsimp only [BinaryCacheFinishRequest.fixed] at h
  simp only [BinaryCacheFinishRequest.framed,BinaryCacheContinuationCore.framed_record,
    BinaryWrapperEmission.listTwo_trace,wrapList,wrap,combine,listCells_append,listCells_under,listCells]
  omega

def seedCost (parsed : Parsed) (rich : Bool) (bits : List Bool) : ℕ :=
  match (BinarySeedPreparationEmission.prepare parsed.1.2.logical bits).1.1.1 with
  | none => 0
  | some held => BinaryResourceArithmeticEntryWork.cache parsed.1 held.2.1 rich

theorem seed_bound (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (bits : List Bool) :
    seedCost parsed rich bits ≤
      2*listCells (BinaryCacheFinishRequest.seed frame parsed hParsed rich bits).1.1.1.2 := by
  simp only [seedCost,BinaryCacheFinishRequest.seed_record,BinaryCacheContinuationCore.seed_record]
  split
  · rename_i hNone
    simp only [hNone]
    omega
  · rename_i held hSome
    have h := framed_bound frame parsed hParsed held.2.1 rich parsed.1.2.logical.request.precision
      held.1.outer held.1.scalar parsed.1.2.logical.header
    dsimp only [BinaryCacheFinishRequest.framed] at h
    simp only [hSome,BinarySeedWrapperEmission.nested_trace,wrap,combine,listCells_append,listCells_under,listCells]
    omega


def rawCost (rich : Bool) (frame bits : List Bool) : ℕ :=
  BinaryParserArithmeticEntryWork.checkedGame frame+
    match (BinaryPromiseOpcodeRequest.backend.run frame).1.1.1.1 with
    | none => 0
    | some parsed => if parsed.2=[] then seedCost parsed rich bits else 0

def generatedCost {S : Type*} (next : S → Bool × S) (rich : Bool) (frame : List Bool) (state : S) : ℕ :=
  BinaryParserArithmeticEntryWork.checkedGame frame+
    match (BinaryPromiseOpcodeRequest.backend.run frame).1.1.1.1 with
    | none => 0
    | some parsed => if parsed.2=[] then seedCost parsed rich
        (BinaryFreshGenerationPlan.generateWithEmission next parsed.1.2.logical state).1.1.1.1 else 0

theorem raw_bound (rich : Bool) (frame bits : List Bool) :
    rawCost rich frame bits ≤ 2*listCells (BinaryPromiseOpcodeRequest.raw rich frame bits).1.1.1.2 := by
  have hp := BinaryParserArithmeticEntryWork.read_bound frame
  simp only [BinaryPromiseOpcodeRequest.raw_record,BinaryRawParserContinuation.raw_record,BinaryPromiseOpcodeRequest.backend]
  split
  · rename_i hNone
    simp only [rawCost,generatedCost,BinaryPromiseOpcodeRequest.backend,hNone,BinaryWrapperEmission.one_trace,wrap,combine,listCells_append,listCells_under,listCells]
    omega
  · rename_i parsed hSome
    split
    · rename_i hTail
      have hOriginal : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed :=
        (congrArg Prod.fst (BinaryRawParserContinuation.read_original BinaryPromiseOpcodeRequest.backend frame)).symm.trans hSome
      have hs := seed_bound frame parsed hOriginal rich bits
      simp only [rawCost,generatedCost,BinaryPromiseOpcodeRequest.backend,hSome,ite_eq_left hTail,BinaryWrapperEmission.two_trace,
        BinarySeedWrapperEmission.three_trace,wrap,combine,listCells_append,listCells_under,listCells]
      omega
    · rename_i hTail
      simp only [rawCost,generatedCost,BinaryPromiseOpcodeRequest.backend,hSome,ite_eq_right hTail,BinaryWrapperEmission.one_trace,
        wrap,combine,listCells_append,listCells_under,listCells]
      omega

theorem parsedRaw_bound (rich : Bool) (frame bits : List Bool) :
    rawCost rich frame bits ≤ 2*listCells (BinaryPromiseOpcodeRequest.parsedRaw rich frame bits).1.1.1.2 := by
  have hp := BinaryParserArithmeticEntryWork.read_bound frame
  simp only [BinaryPromiseOpcodeRequest.parsedRaw_record,BinaryRawParserContinuation.parsedRaw_record,BinaryPromiseOpcodeRequest.backend]
  split
  · rename_i hNone
    simp only [rawCost,generatedCost,BinaryPromiseOpcodeRequest.backend,hNone,BinaryWrapperEmission.one_trace,wrap,combine,listCells_append,listCells_under,listCells]
    omega
  · rename_i parsed hSome
    split
    · rename_i hTail
      have hOriginal : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed :=
        (congrArg Prod.fst (BinaryRawParserContinuation.read_original BinaryPromiseOpcodeRequest.backend frame)).symm.trans hSome
      have hs := seed_bound frame parsed hOriginal rich bits
      simp only [rawCost,generatedCost,BinaryPromiseOpcodeRequest.backend,hSome,ite_eq_left hTail,BinaryWrapperEmission.two_trace,
        BinarySeedWrapperEmission.three_trace,wrap,combine,listCells_append,listCells_under,listCells]
      omega
    · rename_i hTail
      simp only [rawCost,generatedCost,BinaryPromiseOpcodeRequest.backend,hSome,ite_eq_right hTail,BinaryWrapperEmission.one_trace,
        wrap,combine,listCells_append,listCells_under,listCells]
      omega

theorem generated_bound {S : Type*} (next : S → Bool × S) (rich : Bool) (frame : List Bool) (state : S) :
    generatedCost next rich frame state ≤ 2*listCells (BinaryPromiseOpcodeRequest.generated next rich frame state).1.1.1.2 := by
  have hp := BinaryParserArithmeticEntryWork.read_bound frame
  simp only [BinaryPromiseOpcodeRequest.generated_record,BinaryRawParserContinuation.generated_record,BinaryPromiseOpcodeRequest.backend]
  split
  · rename_i hNone
    simp only [rawCost,generatedCost,BinaryPromiseOpcodeRequest.backend,hNone,BinaryWrapperEmission.one_trace,wrap,combine,listCells_append,listCells_under,listCells]
    omega
  · rename_i parsed hSome
    split
    · rename_i hTail
      have hOriginal : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed :=
        (congrArg Prod.fst (BinaryRawParserContinuation.read_original BinaryPromiseOpcodeRequest.backend frame)).symm.trans hSome
      have hs := seed_bound frame parsed hOriginal rich (BinaryFreshGenerationPlan.generateWithEmission next parsed.1.2.logical state).1.1.1.1
      simp only [rawCost,generatedCost,BinaryPromiseOpcodeRequest.backend,hSome,ite_eq_left hTail,BinaryWrapperEmission.two_trace,
        BinarySeedWrapperEmission.three_trace,wrap,combine,listCells_append,listCells_under,listCells]
      omega
    · rename_i hTail
      simp only [rawCost,generatedCost,BinaryPromiseOpcodeRequest.backend,hSome,ite_eq_right hTail,BinaryWrapperEmission.one_trace,
        wrap,combine,listCells_append,listCells_under,listCells]
      omega

theorem parsedGenerated_bound {S : Type*} (next : S → Bool × S) (rich : Bool) (frame : List Bool) (state : S) :
    generatedCost next rich frame state ≤ 2*listCells (BinaryPromiseOpcodeRequest.parsedGenerated next rich frame state).1.1.1.2 := by
  have hp := BinaryParserArithmeticEntryWork.read_bound frame
  simp only [BinaryPromiseOpcodeRequest.parsedGenerated_record,BinaryRawParserContinuation.parsedGenerated_record,BinaryPromiseOpcodeRequest.backend]
  split
  · rename_i hNone
    simp only [rawCost,generatedCost,BinaryPromiseOpcodeRequest.backend,hNone,BinaryWrapperEmission.one_trace,wrap,combine,listCells_append,listCells_under,listCells]
    omega
  · rename_i parsed hSome
    split
    · rename_i hTail
      have hOriginal : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed :=
        (congrArg Prod.fst (BinaryRawParserContinuation.read_original BinaryPromiseOpcodeRequest.backend frame)).symm.trans hSome
      have hs := seed_bound frame parsed hOriginal rich (BinaryFreshGenerationPlan.generateWithEmission next parsed.1.2.logical state).1.1.1.1
      simp only [rawCost,generatedCost,BinaryPromiseOpcodeRequest.backend,hSome,ite_eq_left hTail,BinaryWrapperEmission.two_trace,
        BinarySeedWrapperEmission.three_trace,wrap,combine,listCells_append,listCells_under,listCells]
      omega
    · rename_i hTail
      simp only [rawCost,generatedCost,BinaryPromiseOpcodeRequest.backend,hSome,ite_eq_right hTail,BinaryWrapperEmission.one_trace,
        wrap,combine,listCells_append,listCells_under,listCells]
      omega

def pairCost {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) : ℕ :=
  generatedCost next true frame state+
    generatedCost next false frame (BinaryPromiseOpcodeRequest.generated next true frame state).1.1.1.1.1.2

theorem pair_bound {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    pairCost next frame state ≤ 2*listCells (BinaryPromiseOpcodeRequest.pair next frame state).1.1.1.2 := by
  have hr := generated_bound next true frame state
  have hp := generated_bound next false frame (BinaryPromiseOpcodeRequest.generated next true frame state).1.1.1.1.1.2
  simp only [BinaryPromiseOpcodeRequest.generated_record] at hr hp
  simp only [pairCost,BinaryPromiseOpcodeRequest.pair_record,BinaryRawParserContinuation.pair_record,
    BinaryPromiseOpcodeRequest.generated_record,BinaryWrapperEmission.two_trace,wrap,combine,listCells_append,listCells_under,listCells]
  omega

def parsedPairCost {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) : ℕ :=
  generatedCost next true frame state+
    generatedCost next false frame (BinaryPromiseOpcodeRequest.parsedGenerated next true frame state).1.1.1.1.1.2

theorem parsedPair_bound {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    parsedPairCost next frame state ≤ 2*listCells (BinaryPromiseOpcodeRequest.parsedPair next frame state).1.1.1.2 := by
  have hr := parsedGenerated_bound next true frame state
  have hp := parsedGenerated_bound next false frame (BinaryPromiseOpcodeRequest.parsedGenerated next true frame state).1.1.1.1.1.2
  simp only [BinaryPromiseOpcodeRequest.parsedGenerated_record] at hr hp
  simp only [parsedPairCost,BinaryPromiseOpcodeRequest.parsedPair_record,BinaryRawParserContinuation.parsedPair_record,
    BinaryPromiseOpcodeRequest.parsedGenerated_record,BinaryWrapperEmission.two_trace,wrap,combine,listCells_append,listCells_under,listCells]
  omega

theorem raw_uniform : ∃ C d : ℕ,∀ (rich : Bool) (frame bits : List Bool),
    rawCost rich frame bits ≤ C*(frame.length+1)^d := by
  obtain ⟨C,d,hJoint⟩ := BinaryPromiseOpcodeBounds.raw_joint
  refine ⟨2*C,d,?_⟩
  intro rich frame bits
  have h := raw_bound rich frame bits
  have hj := hJoint rich frame bits
  dsimp only at hj
  simp only [usage,BinaryPRGHeapPrimitiveLifetime.cells] at hj
  simp only [Nat.mul_assoc]
  omega

theorem raw_width : ∃ C d : ℕ,∀ (rich : Bool) (frame bits : List Bool),
    binaryWordWidth (rawCost rich frame bits) ≤ binaryWordWidth (C*(frame.length+1)^d) := by
  obtain ⟨C,d,h⟩ := raw_uniform
  exact ⟨C,d,fun rich frame bits => binaryWordWidth_mono (h rich frame bits)⟩

theorem parsedRaw_uniform : ∃ C d : ℕ,∀ (rich : Bool) (frame bits : List Bool),
    rawCost rich frame bits ≤ C*(frame.length+1)^d := by
  obtain ⟨C,d,hJoint⟩ := BinaryPromiseOpcodeBounds.parsedRaw_joint
  refine ⟨2*C,d,?_⟩
  intro rich frame bits
  have h := parsedRaw_bound rich frame bits
  have hj := hJoint rich frame bits
  dsimp only at hj
  simp only [usage,BinaryPRGHeapPrimitiveLifetime.cells] at hj
  simp only [Nat.mul_assoc]
  omega

theorem parsedRaw_width : ∃ C d : ℕ,∀ (rich : Bool) (frame bits : List Bool),
    binaryWordWidth (rawCost rich frame bits) ≤ binaryWordWidth (C*(frame.length+1)^d) := by
  obtain ⟨C,d,h⟩ := parsedRaw_uniform
  exact ⟨C,d,fun rich frame bits => binaryWordWidth_mono (h rich frame bits)⟩

theorem generated_uniform : ∃ C d : ℕ,∀ {S : Type*} (next : S → Bool × S) (rich : Bool) (frame : List Bool) (state : S),
    generatedCost next rich frame state ≤ C*(frame.length+1)^d := by
  obtain ⟨C,d,hJoint⟩ := BinaryPromiseOpcodeBounds.generated_joint
  refine ⟨2*C,d,?_⟩
  intro S next rich frame state
  have h := generated_bound next rich frame state
  have hj := hJoint next rich frame state
  dsimp only at hj
  simp only [usage,BinaryPRGHeapPrimitiveLifetime.cells] at hj
  simp only [Nat.mul_assoc]
  omega

theorem generated_width : ∃ C d : ℕ,∀ {S : Type*} (next : S → Bool × S) (rich : Bool) (frame : List Bool) (state : S),
    binaryWordWidth (generatedCost next rich frame state) ≤ binaryWordWidth (C*(frame.length+1)^d) := by
  obtain ⟨C,d,h⟩ := generated_uniform
  refine ⟨C,d,?_⟩
  intro S next rich frame state
  exact binaryWordWidth_mono (h next rich frame state)

theorem parsedGenerated_uniform : ∃ C d : ℕ,∀ {S : Type*} (next : S → Bool × S) (rich : Bool) (frame : List Bool) (state : S),
    generatedCost next rich frame state ≤ C*(frame.length+1)^d := by
  obtain ⟨C,d,hJoint⟩ := BinaryPromiseOpcodeBounds.parsedGenerated_joint
  refine ⟨2*C,d,?_⟩
  intro S next rich frame state
  have h := parsedGenerated_bound next rich frame state
  have hj := hJoint next rich frame state
  dsimp only at hj
  simp only [usage,BinaryPRGHeapPrimitiveLifetime.cells] at hj
  simp only [Nat.mul_assoc]
  omega

theorem parsedGenerated_width : ∃ C d : ℕ,∀ {S : Type*} (next : S → Bool × S) (rich : Bool) (frame : List Bool) (state : S),
    binaryWordWidth (generatedCost next rich frame state) ≤ binaryWordWidth (C*(frame.length+1)^d) := by
  obtain ⟨C,d,h⟩ := parsedGenerated_uniform
  refine ⟨C,d,?_⟩
  intro S next rich frame state
  exact binaryWordWidth_mono (h next rich frame state)

theorem pair_uniform : ∃ C d : ℕ,∀ {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S),
    pairCost next frame state ≤ C*(frame.length+1)^d := by
  obtain ⟨C,d,hJoint⟩ := BinaryPromiseOpcodeBounds.pair_joint
  refine ⟨2*C,d,?_⟩
  intro S next frame state
  have h := pair_bound next frame state
  have hj := hJoint next frame state
  dsimp only at hj
  simp only [usage,BinaryPRGHeapPrimitiveLifetime.cells] at hj
  simp only [Nat.mul_assoc]
  omega

theorem pair_width : ∃ C d : ℕ,∀ {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S),
    binaryWordWidth (pairCost next frame state) ≤ binaryWordWidth (C*(frame.length+1)^d) := by
  obtain ⟨C,d,h⟩ := pair_uniform
  refine ⟨C,d,?_⟩
  intro S next frame state
  exact binaryWordWidth_mono (h next frame state)

theorem parsedPair_uniform : ∃ C d : ℕ,∀ {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S),
    parsedPairCost next frame state ≤ C*(frame.length+1)^d := by
  obtain ⟨C,d,hJoint⟩ := BinaryPromiseOpcodeBounds.parsedPair_joint
  refine ⟨2*C,d,?_⟩
  intro S next frame state
  have h := parsedPair_bound next frame state
  have hj := hJoint next frame state
  dsimp only at hj
  simp only [usage,BinaryPRGHeapPrimitiveLifetime.cells] at hj
  simp only [Nat.mul_assoc]
  omega

theorem parsedPair_width : ∃ C d : ℕ,∀ {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S),
    binaryWordWidth (parsedPairCost next frame state) ≤ binaryWordWidth (C*(frame.length+1)^d) := by
  obtain ⟨C,d,h⟩ := parsedPair_uniform
  refine ⟨C,d,?_⟩
  intro S next frame state
  exact binaryWordWidth_mono (h next frame state)

end Blotto.BinaryResourceRequestEntryWork
