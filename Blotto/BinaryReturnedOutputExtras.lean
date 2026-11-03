import Blotto.BinaryNormalizationExtraWork
import Blotto.BinaryCompleteRequestArithmeticEntryWork

/-! Actual output-normalization extras through the selected six complete
interfaces. Old full records and all prior ledger fields are preserved. These
are source/normalization components; metadata evaluation and physical/native
models remain separate. -/
namespace Blotto.BinaryReturnedOutputExtras
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryWordObjectArray (Store)
open BinaryTerminalPhysicalAllowanceCache (Parsed)
set_option autoImplicit false
set_option maxHeartbeats 4000000
attribute [local irreducible] BinaryNormalizedCoordinate.opcode

theorem emit_bound {n : ℕ} (store : Store n) (budget : SignedWord) (indices : List (List Bool)) :
    (BinaryPhysicalOutputMeasured.emitWithExtras store budget indices).2 ≤
      155*(BinaryPhysicalOutputMeasured.emitWithExtras store budget indices).1.2 := by
  induction indices with
  | nil => dsimp only [BinaryPhysicalOutputMeasured.emitWithExtras]; omega
  | cons index indices ih =>
      dsimp only [BinaryPhysicalOutputMeasured.emitWithExtras]
      cases hRead : (BinaryWordObjectArrayAccessMeasured.get store index).1.1 with
      | none => dsimp only; omega
      | some word =>
          dsimp only
          have hs := BinaryNormalizationExtraWork.opcode_bound .mul budget word
          cases hLater : (BinaryPhysicalOutputMeasured.emitWithExtras store budget indices).1.1.1 <;> dsimp only <;> omega

theorem output_bound (budget : SignedWord) (header : List Bool) (words : List SignedWord) :
    (BinaryPhysicalOutputMeasured.outputWithExtras budget header words).2 ≤
      155*(BinaryPhysicalOutputMeasured.outputWithExtras budget header words).1.2 := by
  have h := emit_bound (BinaryWordObjectArrayMeasured.prepare words).1.1 budget
    (BooleanArrayIndexMeasured.enumerate words).1.1
  dsimp only [BinaryPhysicalOutputMeasured.outputWithExtras]
  omega

theorem output_price (budget : SignedWord) (header : List Bool) (words : List SignedWord)
    (hBV : BinaryRationalOpcode.Valid budget) (W : ℕ) (hB : width budget ≤ W)
    (hWords : ∀ word ∈ words,BinaryRationalOpcode.Valid word ∧ width word ≤ W) :
    (BinaryPhysicalOutputMeasured.outputWithExtras budget header words).1.2+
      (BinaryPhysicalOutputMeasured.outputWithExtras budget header words).2 ≤
      156*BinaryPhysicalOutputLifetime.bound words.length W header.length := by
  have he := output_bound budget header words
  have hw := BinaryPhysicalOutputMeasured.output_bound budget header words hBV W hB hWords
  simp only [BinaryPhysicalOutputMeasured.outputWithExtras_compat] at he ⊢
  omega

theorem prefix_mono {n : ℕ} (store : Store n) (budget : SignedWord) (indices : List (List Bool)) (steps : ℕ) :
    (BinaryPhysicalOutputMeasured.emitWithExtras store budget (indices.take steps)).2 ≤
      (BinaryPhysicalOutputMeasured.emitWithExtras store budget indices).2 := by
  induction indices generalizing steps with
  | nil => simp only [List.take_nil]; exact Nat.le_refl _
  | cons index indices ih => cases steps with
    | zero => simp only [List.take_zero,BinaryPhysicalOutputMeasured.emitWithExtras]; exact Nat.zero_le _
    | succ steps =>
        simp only [List.take_succ_cons,BinaryPhysicalOutputMeasured.emitWithExtras]
        cases hRead : (BinaryWordObjectArrayAccessMeasured.get store index).1.1 with
        | none => simp only [hRead]; omega
        | some word =>
            simp only [hRead]
            have h := ih steps
            cases hSmall : (BinaryPhysicalOutputMeasured.emitWithExtras store budget (indices.take steps)).1.1.1 <;>
              cases hWhole : (BinaryPhysicalOutputMeasured.emitWithExtras store budget indices).1.1.1 <;>
              simp only [hSmall,hWhole] <;> omega

theorem prefix_bound {n : ℕ} (store : Store n) (budget : SignedWord) (indices : List (List Bool)) (steps : ℕ) :
    (BinaryPhysicalOutputMeasured.emitWithExtras store budget (indices.take steps)).2 ≤
      155*(BinaryPhysicalOutputMeasured.emitWithExtras store budget indices).1.2 :=
  (prefix_mono store budget indices steps).trans (emit_bound store budget indices)

theorem prefix_width {n : ℕ} (store : Store n) (budget : SignedWord) (indices : List (List Bool)) (steps : ℕ) :
    binaryWordWidth (BinaryPhysicalOutputMeasured.emitWithExtras store budget (indices.take steps)).2 ≤
      binaryWordWidth (155*(BinaryPhysicalOutputMeasured.emitWithExtras store budget indices).1.2) :=
  binaryWordWidth_mono (prefix_bound store budget indices steps)

theorem framed_bound {E : Type*} [Zero E] [Add E] (backend : BinaryCacheContinuationCore.Backend E)
    (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (header : BinaryPRGHeaderFrame.Header parsed.1.1) :
    (BinaryCacheContinuationCore.framedWithOutputExtras backend frame parsed hParsed seed rich K outer scalar header).2 ≤
      155*(BinaryCacheContinuationCore.framedWithOutputExtras backend frame parsed hParsed seed rich K outer scalar header).1.1.1.2 := by
  let child := BinaryCacheContinuationCore.fixed backend frame parsed hParsed seed rich K outer scalar
  let returned := child.1
  let drawn := returned.1
  have h := output_bound parsed.1.2.logical.request.prepared.original.a header.bytes drawn.1.1.1.1.data.toList
  dsimp only [drawn,returned,child] at h
  simp only [BinaryCacheContinuationCore.framedWithOutputExtras_record]
  omega

theorem seed_bound {E : Type*} [Zero E] [Add E] (backend : BinaryCacheContinuationCore.Backend E)
    (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (bits : List Bool) :
    (BinaryCacheContinuationCore.seedWithOutputExtras backend frame parsed hParsed rich bits).2 ≤
      155*(BinaryCacheContinuationCore.seedWithOutputExtras backend frame parsed hParsed rich bits).1.1.1.2 := by
  simp only [BinaryCacheContinuationCore.seedWithOutputExtras_record]
  cases h : (BinarySeedPreparationEmission.prepare parsed.1.2.logical bits).1.1.1 with
  | none => dsimp only; omega
  | some held =>
      dsimp only
      have he := framed_bound backend frame parsed hParsed held.2.1 rich parsed.1.2.logical.request.precision
        held.1.outer held.1.scalar parsed.1.2.logical.header
      omega

theorem cache_seed_bound (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (bits : List Bool) :
    (BinaryCacheFinishRequest.seedWithOutputExtras frame parsed hParsed rich bits).2 ≤
      155*(BinaryCacheFinishRequest.seedWithOutputExtras frame parsed hParsed rich bits).1.1.1.2 :=
  seed_bound BinaryCacheFinishRequest.backend frame parsed hParsed rich bits

theorem parser_raw_bound {E : Type*} [Zero E] [Add E] (backend : BinaryRawParserContinuation.Backend E) (rich : Bool) (frame bits : List Bool) :
    (BinaryRawParserContinuation.rawWithOutputExtras backend rich frame bits).2 ≤ 155*(BinaryRawParserContinuation.rawWithOutputExtras backend rich frame bits).1.1.1.2 := by
  simp only [BinaryRawParserContinuation.rawWithOutputExtras_record]
  split
  · dsimp only; omega
  · rename_i parsed hParsed
    split
    · have hOriginal : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed :=
        (congrArg Prod.fst (BinaryRawParserContinuation.read_original backend frame)).symm.trans hParsed
      have hc := cache_seed_bound frame parsed hOriginal rich bits
      dsimp only
      omega
    · dsimp only; omega

theorem parser_parsedRaw_bound {E : Type*} [Zero E] [Add E] (backend : BinaryRawParserContinuation.Backend E) (rich : Bool) (frame bits : List Bool) :
    (BinaryRawParserContinuation.parsedRawWithOutputExtras backend rich frame bits).2 ≤ 155*(BinaryRawParserContinuation.parsedRawWithOutputExtras backend rich frame bits).1.1.1.2 := by
  simp only [BinaryRawParserContinuation.parsedRawWithOutputExtras_record]
  split
  · dsimp only; omega
  · rename_i parsed hParsed
    split
    · have hOriginal : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed :=
        (congrArg Prod.fst (BinaryRawParserContinuation.read_original backend frame)).symm.trans hParsed
      have hc := cache_seed_bound frame parsed hOriginal rich bits
      dsimp only
      omega
    · dsimp only; omega

theorem parser_generated_bound {E : Type*} [Zero E] [Add E] (backend : BinaryRawParserContinuation.Backend E) {S : Type*} (next : S → Bool × S) (rich : Bool) (frame : List Bool) (state : S) :
    (BinaryRawParserContinuation.generatedWithOutputExtras backend next rich frame state).2 ≤ 155*(BinaryRawParserContinuation.generatedWithOutputExtras backend next rich frame state).1.1.1.2 := by
  simp only [BinaryRawParserContinuation.generatedWithOutputExtras_record]
  split
  · dsimp only; omega
  · rename_i parsed hParsed
    split
    · have hOriginal : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed :=
        (congrArg Prod.fst (BinaryRawParserContinuation.read_original backend frame)).symm.trans hParsed
      let generation := BinaryFreshGenerationPlan.generateWithEmission next parsed.1.2.logical state
      let generated := generation.1
      have hc := cache_seed_bound frame parsed hOriginal rich generated.1.1.1
      dsimp only [generated,generation] at hc
      dsimp only
      omega
    · dsimp only; omega

theorem parser_parsedGenerated_bound {E : Type*} [Zero E] [Add E] (backend : BinaryRawParserContinuation.Backend E) {S : Type*} (next : S → Bool × S) (rich : Bool) (frame : List Bool) (state : S) :
    (BinaryRawParserContinuation.parsedGeneratedWithOutputExtras backend next rich frame state).2 ≤ 155*(BinaryRawParserContinuation.parsedGeneratedWithOutputExtras backend next rich frame state).1.1.1.2 := by
  simp only [BinaryRawParserContinuation.parsedGeneratedWithOutputExtras_record]
  split
  · dsimp only; omega
  · rename_i parsed hParsed
    split
    · have hOriginal : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed :=
        (congrArg Prod.fst (BinaryRawParserContinuation.read_original backend frame)).symm.trans hParsed
      let generation := BinaryFreshGenerationPlan.generateWithEmission next parsed.1.2.logical state
      let generated := generation.1
      have hc := cache_seed_bound frame parsed hOriginal rich generated.1.1.1
      dsimp only [generated,generation] at hc
      dsimp only
      omega
    · dsimp only; omega

theorem parser_pair_bound {E : Type*} [Zero E] [Add E] (backend : BinaryRawParserContinuation.Backend E)
    {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    (BinaryRawParserContinuation.pairWithOutputExtras backend next frame state).2 ≤ 155*(BinaryRawParserContinuation.pairWithOutputExtras backend next frame state).1.1.1.2 := by
  let first := BinaryRawParserContinuation.generatedWithOutputExtras backend next true frame state
  let rich := first.1.1
  have hFirst := parser_generated_bound backend next true frame state
  have hSecond := parser_generated_bound backend next false frame rich.1.1.1.1.2
  dsimp only [rich,first] at hSecond
  simp only [BinaryRawParserContinuation.pairWithOutputExtras_record]
  omega

theorem parser_parsedPair_bound {E : Type*} [Zero E] [Add E] (backend : BinaryRawParserContinuation.Backend E)
    {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    (BinaryRawParserContinuation.parsedPairWithOutputExtras backend next frame state).2 ≤ 155*(BinaryRawParserContinuation.parsedPairWithOutputExtras backend next frame state).1.1.1.2 := by
  let first := BinaryRawParserContinuation.parsedGeneratedWithOutputExtras backend next true frame state
  let rich := first.1.1
  have hFirst := parser_parsedGenerated_bound backend next true frame state
  have hSecond := parser_parsedGenerated_bound backend next false frame rich.1.1.1.1.2
  dsimp only [rich,first] at hSecond
  simp only [BinaryRawParserContinuation.parsedPairWithOutputExtras_record]
  omega

theorem raw_bound (rich : Bool) (frame bits : List Bool) :
    (BinaryPromiseOpcodeRequest.rawWithOutputExtras rich frame bits).2 ≤ 155*(BinaryPromiseOpcodeRequest.rawWithOutputExtras rich frame bits).1.1.1.2 :=
  parser_raw_bound BinaryPromiseOpcodeRequest.backend rich frame bits

theorem parsedRaw_bound (rich : Bool) (frame bits : List Bool) :
    (BinaryPromiseOpcodeRequest.parsedRawWithOutputExtras rich frame bits).2 ≤ 155*(BinaryPromiseOpcodeRequest.parsedRawWithOutputExtras rich frame bits).1.1.1.2 :=
  parser_parsedRaw_bound BinaryPromiseOpcodeRequest.backend rich frame bits

theorem generated_bound {S : Type*} (next : S → Bool × S) (rich : Bool) (frame : List Bool) (state : S) :
    (BinaryPromiseOpcodeRequest.generatedWithOutputExtras next rich frame state).2 ≤ 155*(BinaryPromiseOpcodeRequest.generatedWithOutputExtras next rich frame state).1.1.1.2 :=
  parser_generated_bound BinaryPromiseOpcodeRequest.backend next rich frame state

theorem parsedGenerated_bound {S : Type*} (next : S → Bool × S) (rich : Bool) (frame : List Bool) (state : S) :
    (BinaryPromiseOpcodeRequest.parsedGeneratedWithOutputExtras next rich frame state).2 ≤ 155*(BinaryPromiseOpcodeRequest.parsedGeneratedWithOutputExtras next rich frame state).1.1.1.2 :=
  parser_parsedGenerated_bound BinaryPromiseOpcodeRequest.backend next rich frame state

theorem pair_bound {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    (BinaryPromiseOpcodeRequest.pairWithOutputExtras next frame state).2 ≤ 155*(BinaryPromiseOpcodeRequest.pairWithOutputExtras next frame state).1.1.1.2 :=
  parser_pair_bound BinaryPromiseOpcodeRequest.backend next frame state

theorem parsedPair_bound {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    (BinaryPromiseOpcodeRequest.parsedPairWithOutputExtras next frame state).2 ≤ 155*(BinaryPromiseOpcodeRequest.parsedPairWithOutputExtras next frame state).1.1.1.2 :=
  parser_parsedPair_bound BinaryPromiseOpcodeRequest.backend next frame state

theorem join_source_component (source total extra cap : ℕ)
    (hSource : source ≤ total) (hExtra : extra ≤ 155*source) (hTotal : total ≤ cap) :
    total+extra ≤ 156*cap ∧ binaryWordWidth extra ≤ binaryWordWidth (156*cap) := by
  have h : total+extra ≤ 156*cap := by omega
  exact ⟨h,binaryWordWidth_mono (by omega)⟩

attribute [local irreducible]
  BinaryPromiseOpcodeRequest.raw
  BinaryPromiseOpcodeRequest.parsedRaw
  BinaryPromiseOpcodeRequest.generated
  BinaryPromiseOpcodeRequest.parsedGenerated
  BinaryPromiseOpcodeRequest.pair
  BinaryPromiseOpcodeRequest.parsedPair
  BinaryPromiseOpcodeRequest.rawWithOutputExtras
  BinaryPromiseOpcodeRequest.parsedRawWithOutputExtras
  BinaryPromiseOpcodeRequest.generatedWithOutputExtras
  BinaryPromiseOpcodeRequest.parsedGeneratedWithOutputExtras
  BinaryPromiseOpcodeRequest.pairWithOutputExtras
  BinaryPromiseOpcodeRequest.parsedPairWithOutputExtras
  BinaryCompleteRequestArithmeticEntryWork.rawCost
  BinaryCompleteRequestArithmeticEntryWork.generatedCost
  BinaryCompleteRequestArithmeticEntryWork.pairCost
  BinaryCompleteRequestArithmeticEntryWork.parsedPairCost
attribute [local irreducible] BinaryPRGHeapTraceUsage.usage BinarySamplerExecutionCharges.total
  BinaryGenerationExecutionCharges.total BinaryBigEndian.littleValue
set_option maxHeartbeats 300000

theorem raw_complete_joint : ∃ C d : ℕ,∀ (rich : Bool) (frame bits : List Bool),
    let returned := BinaryPromiseOpcodeRequest.rawWithOutputExtras rich frame bits
    let produced := returned.1
    (BinaryCompleteRequestArithmeticEntryWork.rawCost rich frame bits+produced.1.1.2+BinaryBigEndian.littleValue produced.1.1.1.1.2+usage produced.1.1.1.2+
      BinarySamplerExecutionCharges.total produced.1.2+produced.2.1.1+produced.2.1.2+produced.2.2.1.1.1.1.1.1.1.1.1.1+produced.2.2.1.1.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.2+produced.2.2.1.1.1.1.2+produced.2.2.1.1.1.2+produced.2.2.1.1.2+produced.2.2.1.2+produced.2.2.2.1.1.1.1.1.1+produced.2.2.2.1.1.1.1.1.2+produced.2.2.2.1.1.1.1.2+produced.2.2.2.1.1.1.2+produced.2.2.2.1.1.2+produced.2.2.2.1.2+produced.2.2.2.2)+returned.2 ≤ C*(frame.length+1)^d ∧
      binaryWordWidth returned.2 ≤ binaryWordWidth (C*(frame.length+1)^d) := by
  obtain ⟨C,d,hOld⟩ := BinaryCompleteRequestArithmeticEntryWork.raw_complete_joint
  refine ⟨156*C,d,?_⟩
  intro rich frame bits
  have ho := hOld rich frame bits
  have he := raw_bound rich frame bits
  dsimp only at ho ⊢
  simp only [BinaryPromiseOpcodeRequest.rawWithOutputExtras_compat,Nat.mul_assoc] at he ⊢
  generalize (BinaryPromiseOpcodeRequest.rawWithOutputExtras rich frame bits).2 = extra at he ⊢
  generalize BinaryPromiseOpcodeRequest.raw rich frame bits = previous at ho he ⊢
  have hSource : previous.1.1.2 ≤ BinaryCompleteRequestArithmeticEntryWork.rawCost rich frame bits+previous.1.1.2+BinaryBigEndian.littleValue previous.1.1.1.1.2+usage previous.1.1.1.2+
      BinarySamplerExecutionCharges.total previous.1.2+previous.2.1.1+previous.2.1.2+previous.2.2.1.1.1.1.1.1.1.1.1.1+previous.2.2.1.1.1.1.1.1.1.1.1.2+previous.2.2.1.1.1.1.1.1.1.1.2+previous.2.2.1.1.1.1.1.1.1.2+previous.2.2.1.1.1.1.1.1.2+previous.2.2.1.1.1.1.1.2+previous.2.2.1.1.1.1.2+previous.2.2.1.1.1.2+previous.2.2.1.1.2+previous.2.2.1.2+previous.2.2.2.1.1.1.1.1.1+previous.2.2.2.1.1.1.1.1.2+previous.2.2.2.1.1.1.1.2+previous.2.2.2.1.1.1.2+previous.2.2.2.1.1.2+previous.2.2.2.1.2+previous.2.2.2.2 := by
    simpa only [Nat.add_assoc] using
      (Nat.le_add_left previous.1.1.2 (BinaryCompleteRequestArithmeticEntryWork.rawCost rich frame bits)).trans
        (Nat.le_add_right (BinaryCompleteRequestArithmeticEntryWork.rawCost rich frame bits+previous.1.1.2) (BinaryBigEndian.littleValue previous.1.1.1.1.2 + usage previous.1.1.1.2 + 
      BinarySamplerExecutionCharges.total previous.1.2 + previous.2.1.1 + previous.2.1.2 + previous.2.2.1.1.1.1.1.1.1.1.1.1 + previous.2.2.1.1.1.1.1.1.1.1.1.2 + previous.2.2.1.1.1.1.1.1.1.1.2 + previous.2.2.1.1.1.1.1.1.1.2 + previous.2.2.1.1.1.1.1.1.2 + previous.2.2.1.1.1.1.1.2 + previous.2.2.1.1.1.1.2 + previous.2.2.1.1.1.2 + previous.2.2.1.1.2 + previous.2.2.1.2 + previous.2.2.2.1.1.1.1.1.1 + previous.2.2.2.1.1.1.1.1.2 + previous.2.2.2.1.1.1.1.2 + previous.2.2.2.1.1.1.2 + previous.2.2.2.1.1.2 + previous.2.2.2.1.2 + previous.2.2.2.2))
  exact join_source_component previous.1.1.2 (BinaryCompleteRequestArithmeticEntryWork.rawCost rich frame bits+previous.1.1.2+BinaryBigEndian.littleValue previous.1.1.1.1.2+usage previous.1.1.1.2+
      BinarySamplerExecutionCharges.total previous.1.2+previous.2.1.1+previous.2.1.2+previous.2.2.1.1.1.1.1.1.1.1.1.1+previous.2.2.1.1.1.1.1.1.1.1.1.2+previous.2.2.1.1.1.1.1.1.1.1.2+previous.2.2.1.1.1.1.1.1.1.2+previous.2.2.1.1.1.1.1.1.2+previous.2.2.1.1.1.1.1.2+previous.2.2.1.1.1.1.2+previous.2.2.1.1.1.2+previous.2.2.1.1.2+previous.2.2.1.2+previous.2.2.2.1.1.1.1.1.1+previous.2.2.2.1.1.1.1.1.2+previous.2.2.2.1.1.1.1.2+previous.2.2.2.1.1.1.2+previous.2.2.2.1.1.2+previous.2.2.2.1.2+previous.2.2.2.2) extra (C*(frame.length+1)^d) hSource he ho


theorem parsedRaw_complete_joint : ∃ C d : ℕ,∀ (rich : Bool) (frame bits : List Bool),
    let returned := BinaryPromiseOpcodeRequest.parsedRawWithOutputExtras rich frame bits
    let produced := returned.1
    (BinaryCompleteRequestArithmeticEntryWork.rawCost rich frame bits+produced.1.1.2+BinaryBigEndian.littleValue produced.1.1.1.1.2+usage produced.1.1.1.2+
      BinarySamplerExecutionCharges.total produced.1.2+produced.2.1.1+produced.2.1.2+produced.2.2.1.1.1.1.1.1.1.1.1.1+produced.2.2.1.1.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.2+produced.2.2.1.1.1.1.2+produced.2.2.1.1.1.2+produced.2.2.1.1.2+produced.2.2.1.2+produced.2.2.2.1.1.1.1.1.1+produced.2.2.2.1.1.1.1.1.2+produced.2.2.2.1.1.1.1.2+produced.2.2.2.1.1.1.2+produced.2.2.2.1.1.2+produced.2.2.2.1.2+produced.2.2.2.2)+returned.2 ≤ C*(frame.length+1)^d ∧
      binaryWordWidth returned.2 ≤ binaryWordWidth (C*(frame.length+1)^d) := by
  obtain ⟨C,d,hOld⟩ := BinaryCompleteRequestArithmeticEntryWork.parsedRaw_complete_joint
  refine ⟨156*C,d,?_⟩
  intro rich frame bits
  have ho := hOld rich frame bits
  have he := parsedRaw_bound rich frame bits
  dsimp only at ho ⊢
  simp only [BinaryPromiseOpcodeRequest.parsedRawWithOutputExtras_compat,Nat.mul_assoc] at he ⊢
  generalize (BinaryPromiseOpcodeRequest.parsedRawWithOutputExtras rich frame bits).2 = extra at he ⊢
  generalize BinaryPromiseOpcodeRequest.parsedRaw rich frame bits = previous at ho he ⊢
  have hSource : previous.1.1.2 ≤ BinaryCompleteRequestArithmeticEntryWork.rawCost rich frame bits+previous.1.1.2+BinaryBigEndian.littleValue previous.1.1.1.1.2+usage previous.1.1.1.2+
      BinarySamplerExecutionCharges.total previous.1.2+previous.2.1.1+previous.2.1.2+previous.2.2.1.1.1.1.1.1.1.1.1.1+previous.2.2.1.1.1.1.1.1.1.1.1.2+previous.2.2.1.1.1.1.1.1.1.1.2+previous.2.2.1.1.1.1.1.1.1.2+previous.2.2.1.1.1.1.1.1.2+previous.2.2.1.1.1.1.1.2+previous.2.2.1.1.1.1.2+previous.2.2.1.1.1.2+previous.2.2.1.1.2+previous.2.2.1.2+previous.2.2.2.1.1.1.1.1.1+previous.2.2.2.1.1.1.1.1.2+previous.2.2.2.1.1.1.1.2+previous.2.2.2.1.1.1.2+previous.2.2.2.1.1.2+previous.2.2.2.1.2+previous.2.2.2.2 := by
    simpa only [Nat.add_assoc] using
      (Nat.le_add_left previous.1.1.2 (BinaryCompleteRequestArithmeticEntryWork.rawCost rich frame bits)).trans
        (Nat.le_add_right (BinaryCompleteRequestArithmeticEntryWork.rawCost rich frame bits+previous.1.1.2) (BinaryBigEndian.littleValue previous.1.1.1.1.2 + usage previous.1.1.1.2 + 
      BinarySamplerExecutionCharges.total previous.1.2 + previous.2.1.1 + previous.2.1.2 + previous.2.2.1.1.1.1.1.1.1.1.1.1 + previous.2.2.1.1.1.1.1.1.1.1.1.2 + previous.2.2.1.1.1.1.1.1.1.1.2 + previous.2.2.1.1.1.1.1.1.1.2 + previous.2.2.1.1.1.1.1.1.2 + previous.2.2.1.1.1.1.1.2 + previous.2.2.1.1.1.1.2 + previous.2.2.1.1.1.2 + previous.2.2.1.1.2 + previous.2.2.1.2 + previous.2.2.2.1.1.1.1.1.1 + previous.2.2.2.1.1.1.1.1.2 + previous.2.2.2.1.1.1.1.2 + previous.2.2.2.1.1.1.2 + previous.2.2.2.1.1.2 + previous.2.2.2.1.2 + previous.2.2.2.2))
  exact join_source_component previous.1.1.2 (BinaryCompleteRequestArithmeticEntryWork.rawCost rich frame bits+previous.1.1.2+BinaryBigEndian.littleValue previous.1.1.1.1.2+usage previous.1.1.1.2+
      BinarySamplerExecutionCharges.total previous.1.2+previous.2.1.1+previous.2.1.2+previous.2.2.1.1.1.1.1.1.1.1.1.1+previous.2.2.1.1.1.1.1.1.1.1.1.2+previous.2.2.1.1.1.1.1.1.1.1.2+previous.2.2.1.1.1.1.1.1.1.2+previous.2.2.1.1.1.1.1.1.2+previous.2.2.1.1.1.1.1.2+previous.2.2.1.1.1.1.2+previous.2.2.1.1.1.2+previous.2.2.1.1.2+previous.2.2.1.2+previous.2.2.2.1.1.1.1.1.1+previous.2.2.2.1.1.1.1.1.2+previous.2.2.2.1.1.1.1.2+previous.2.2.2.1.1.1.2+previous.2.2.2.1.1.2+previous.2.2.2.1.2+previous.2.2.2.2) extra (C*(frame.length+1)^d) hSource he ho


theorem generated_complete_joint : ∃ C d : ℕ,∀ {S : Type*} (next : S → Bool × S) (rich : Bool) (frame : List Bool) (state : S),
    let returned := BinaryPromiseOpcodeRequest.generatedWithOutputExtras next rich frame state
    let produced := returned.1
    (BinaryCompleteRequestArithmeticEntryWork.generatedCost next rich frame state+produced.1.1.2+BinaryBigEndian.littleValue produced.1.1.1.1.2+usage produced.1.1.1.2+
      BinaryGenerationExecutionCharges.total produced.1.2+produced.2.1.1+produced.2.1.2+produced.2.2.1.1.1.1.1.1.1.1.1.1+produced.2.2.1.1.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.2+produced.2.2.1.1.1.1.2+produced.2.2.1.1.1.2+produced.2.2.1.1.2+produced.2.2.1.2+produced.2.2.2.1.1.1.1.1.1+produced.2.2.2.1.1.1.1.1.2+produced.2.2.2.1.1.1.1.2+produced.2.2.2.1.1.1.2+produced.2.2.2.1.1.2+produced.2.2.2.1.2+produced.2.2.2.2)+returned.2 ≤ C*(frame.length+1)^d ∧
      binaryWordWidth returned.2 ≤ binaryWordWidth (C*(frame.length+1)^d) := by
  obtain ⟨C,d,hOld⟩ := BinaryCompleteRequestArithmeticEntryWork.generated_complete_joint
  refine ⟨156*C,d,?_⟩
  intro S next rich frame state
  have ho := hOld next rich frame state
  have he := generated_bound next rich frame state
  dsimp only at ho ⊢
  simp only [BinaryPromiseOpcodeRequest.generatedWithOutputExtras_compat,Nat.mul_assoc] at he ⊢
  generalize (BinaryPromiseOpcodeRequest.generatedWithOutputExtras next rich frame state).2 = extra at he ⊢
  generalize BinaryPromiseOpcodeRequest.generated next rich frame state = previous at ho he ⊢
  have hSource : previous.1.1.2 ≤ BinaryCompleteRequestArithmeticEntryWork.generatedCost next rich frame state+previous.1.1.2+BinaryBigEndian.littleValue previous.1.1.1.1.2+usage previous.1.1.1.2+
      BinaryGenerationExecutionCharges.total previous.1.2+previous.2.1.1+previous.2.1.2+previous.2.2.1.1.1.1.1.1.1.1.1.1+previous.2.2.1.1.1.1.1.1.1.1.1.2+previous.2.2.1.1.1.1.1.1.1.1.2+previous.2.2.1.1.1.1.1.1.1.2+previous.2.2.1.1.1.1.1.1.2+previous.2.2.1.1.1.1.1.2+previous.2.2.1.1.1.1.2+previous.2.2.1.1.1.2+previous.2.2.1.1.2+previous.2.2.1.2+previous.2.2.2.1.1.1.1.1.1+previous.2.2.2.1.1.1.1.1.2+previous.2.2.2.1.1.1.1.2+previous.2.2.2.1.1.1.2+previous.2.2.2.1.1.2+previous.2.2.2.1.2+previous.2.2.2.2 := by
    simpa only [Nat.add_assoc] using
      (Nat.le_add_left previous.1.1.2 (BinaryCompleteRequestArithmeticEntryWork.generatedCost next rich frame state)).trans
        (Nat.le_add_right (BinaryCompleteRequestArithmeticEntryWork.generatedCost next rich frame state+previous.1.1.2) (BinaryBigEndian.littleValue previous.1.1.1.1.2 + usage previous.1.1.1.2 + 
      BinaryGenerationExecutionCharges.total previous.1.2 + previous.2.1.1 + previous.2.1.2 + previous.2.2.1.1.1.1.1.1.1.1.1.1 + previous.2.2.1.1.1.1.1.1.1.1.1.2 + previous.2.2.1.1.1.1.1.1.1.1.2 + previous.2.2.1.1.1.1.1.1.1.2 + previous.2.2.1.1.1.1.1.1.2 + previous.2.2.1.1.1.1.1.2 + previous.2.2.1.1.1.1.2 + previous.2.2.1.1.1.2 + previous.2.2.1.1.2 + previous.2.2.1.2 + previous.2.2.2.1.1.1.1.1.1 + previous.2.2.2.1.1.1.1.1.2 + previous.2.2.2.1.1.1.1.2 + previous.2.2.2.1.1.1.2 + previous.2.2.2.1.1.2 + previous.2.2.2.1.2 + previous.2.2.2.2))
  exact join_source_component previous.1.1.2 (BinaryCompleteRequestArithmeticEntryWork.generatedCost next rich frame state+previous.1.1.2+BinaryBigEndian.littleValue previous.1.1.1.1.2+usage previous.1.1.1.2+
      BinaryGenerationExecutionCharges.total previous.1.2+previous.2.1.1+previous.2.1.2+previous.2.2.1.1.1.1.1.1.1.1.1.1+previous.2.2.1.1.1.1.1.1.1.1.1.2+previous.2.2.1.1.1.1.1.1.1.1.2+previous.2.2.1.1.1.1.1.1.1.2+previous.2.2.1.1.1.1.1.1.2+previous.2.2.1.1.1.1.1.2+previous.2.2.1.1.1.1.2+previous.2.2.1.1.1.2+previous.2.2.1.1.2+previous.2.2.1.2+previous.2.2.2.1.1.1.1.1.1+previous.2.2.2.1.1.1.1.1.2+previous.2.2.2.1.1.1.1.2+previous.2.2.2.1.1.1.2+previous.2.2.2.1.1.2+previous.2.2.2.1.2+previous.2.2.2.2) extra (C*(frame.length+1)^d) hSource he ho


theorem parsedGenerated_complete_joint : ∃ C d : ℕ,∀ {S : Type*} (next : S → Bool × S) (rich : Bool) (frame : List Bool) (state : S),
    let returned := BinaryPromiseOpcodeRequest.parsedGeneratedWithOutputExtras next rich frame state
    let produced := returned.1
    (BinaryCompleteRequestArithmeticEntryWork.generatedCost next rich frame state+produced.1.1.2+BinaryBigEndian.littleValue produced.1.1.1.1.2+usage produced.1.1.1.2+
      BinaryGenerationExecutionCharges.total produced.1.2+produced.2.1.1+produced.2.1.2+produced.2.2.1.1.1.1.1.1.1.1.1.1+produced.2.2.1.1.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.2+produced.2.2.1.1.1.1.2+produced.2.2.1.1.1.2+produced.2.2.1.1.2+produced.2.2.1.2+produced.2.2.2.1.1.1.1.1.1+produced.2.2.2.1.1.1.1.1.2+produced.2.2.2.1.1.1.1.2+produced.2.2.2.1.1.1.2+produced.2.2.2.1.1.2+produced.2.2.2.1.2+produced.2.2.2.2)+returned.2 ≤ C*(frame.length+1)^d ∧
      binaryWordWidth returned.2 ≤ binaryWordWidth (C*(frame.length+1)^d) := by
  obtain ⟨C,d,hOld⟩ := BinaryCompleteRequestArithmeticEntryWork.parsedGenerated_complete_joint
  refine ⟨156*C,d,?_⟩
  intro S next rich frame state
  have ho := hOld next rich frame state
  have he := parsedGenerated_bound next rich frame state
  dsimp only at ho ⊢
  simp only [BinaryPromiseOpcodeRequest.parsedGeneratedWithOutputExtras_compat,Nat.mul_assoc] at he ⊢
  generalize (BinaryPromiseOpcodeRequest.parsedGeneratedWithOutputExtras next rich frame state).2 = extra at he ⊢
  generalize BinaryPromiseOpcodeRequest.parsedGenerated next rich frame state = previous at ho he ⊢
  have hSource : previous.1.1.2 ≤ BinaryCompleteRequestArithmeticEntryWork.generatedCost next rich frame state+previous.1.1.2+BinaryBigEndian.littleValue previous.1.1.1.1.2+usage previous.1.1.1.2+
      BinaryGenerationExecutionCharges.total previous.1.2+previous.2.1.1+previous.2.1.2+previous.2.2.1.1.1.1.1.1.1.1.1.1+previous.2.2.1.1.1.1.1.1.1.1.1.2+previous.2.2.1.1.1.1.1.1.1.1.2+previous.2.2.1.1.1.1.1.1.1.2+previous.2.2.1.1.1.1.1.1.2+previous.2.2.1.1.1.1.1.2+previous.2.2.1.1.1.1.2+previous.2.2.1.1.1.2+previous.2.2.1.1.2+previous.2.2.1.2+previous.2.2.2.1.1.1.1.1.1+previous.2.2.2.1.1.1.1.1.2+previous.2.2.2.1.1.1.1.2+previous.2.2.2.1.1.1.2+previous.2.2.2.1.1.2+previous.2.2.2.1.2+previous.2.2.2.2 := by
    simpa only [Nat.add_assoc] using
      (Nat.le_add_left previous.1.1.2 (BinaryCompleteRequestArithmeticEntryWork.generatedCost next rich frame state)).trans
        (Nat.le_add_right (BinaryCompleteRequestArithmeticEntryWork.generatedCost next rich frame state+previous.1.1.2) (BinaryBigEndian.littleValue previous.1.1.1.1.2 + usage previous.1.1.1.2 + 
      BinaryGenerationExecutionCharges.total previous.1.2 + previous.2.1.1 + previous.2.1.2 + previous.2.2.1.1.1.1.1.1.1.1.1.1 + previous.2.2.1.1.1.1.1.1.1.1.1.2 + previous.2.2.1.1.1.1.1.1.1.1.2 + previous.2.2.1.1.1.1.1.1.1.2 + previous.2.2.1.1.1.1.1.1.2 + previous.2.2.1.1.1.1.1.2 + previous.2.2.1.1.1.1.2 + previous.2.2.1.1.1.2 + previous.2.2.1.1.2 + previous.2.2.1.2 + previous.2.2.2.1.1.1.1.1.1 + previous.2.2.2.1.1.1.1.1.2 + previous.2.2.2.1.1.1.1.2 + previous.2.2.2.1.1.1.2 + previous.2.2.2.1.1.2 + previous.2.2.2.1.2 + previous.2.2.2.2))
  exact join_source_component previous.1.1.2 (BinaryCompleteRequestArithmeticEntryWork.generatedCost next rich frame state+previous.1.1.2+BinaryBigEndian.littleValue previous.1.1.1.1.2+usage previous.1.1.1.2+
      BinaryGenerationExecutionCharges.total previous.1.2+previous.2.1.1+previous.2.1.2+previous.2.2.1.1.1.1.1.1.1.1.1.1+previous.2.2.1.1.1.1.1.1.1.1.1.2+previous.2.2.1.1.1.1.1.1.1.1.2+previous.2.2.1.1.1.1.1.1.1.2+previous.2.2.1.1.1.1.1.1.2+previous.2.2.1.1.1.1.1.2+previous.2.2.1.1.1.1.2+previous.2.2.1.1.1.2+previous.2.2.1.1.2+previous.2.2.1.2+previous.2.2.2.1.1.1.1.1.1+previous.2.2.2.1.1.1.1.1.2+previous.2.2.2.1.1.1.1.2+previous.2.2.2.1.1.1.2+previous.2.2.2.1.1.2+previous.2.2.2.1.2+previous.2.2.2.2) extra (C*(frame.length+1)^d) hSource he ho


theorem pair_complete_joint : ∃ C d : ℕ,∀ {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S),
    let returned := BinaryPromiseOpcodeRequest.pairWithOutputExtras next frame state
    let produced := returned.1
    (BinaryCompleteRequestArithmeticEntryWork.pairCost next frame state+produced.1.1.2+BinaryBigEndian.littleValue produced.1.1.1.1.2.1+BinaryBigEndian.littleValue produced.1.1.1.1.2.2+usage produced.1.1.1.2+
      BinaryGenerationExecutionCharges.total produced.1.2+produced.2.1.1+produced.2.1.2+produced.2.2.1.1.1.1.1.1.1.1.1.1+produced.2.2.1.1.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.2+produced.2.2.1.1.1.1.2+produced.2.2.1.1.1.2+produced.2.2.1.1.2+produced.2.2.1.2+produced.2.2.2.1.1.1.1.1.1+produced.2.2.2.1.1.1.1.1.2+produced.2.2.2.1.1.1.1.2+produced.2.2.2.1.1.1.2+produced.2.2.2.1.1.2+produced.2.2.2.1.2+produced.2.2.2.2)+returned.2 ≤ C*(frame.length+1)^d ∧
      binaryWordWidth returned.2 ≤ binaryWordWidth (C*(frame.length+1)^d) := by
  obtain ⟨C,d,hOld⟩ := BinaryCompleteRequestArithmeticEntryWork.pair_complete_joint
  refine ⟨156*C,d,?_⟩
  intro S next frame state
  have ho := hOld next frame state
  have he := pair_bound next frame state
  dsimp only at ho ⊢
  simp only [BinaryPromiseOpcodeRequest.pairWithOutputExtras_compat,Nat.mul_assoc] at he ⊢
  generalize (BinaryPromiseOpcodeRequest.pairWithOutputExtras next frame state).2 = extra at he ⊢
  generalize BinaryPromiseOpcodeRequest.pair next frame state = previous at ho he ⊢
  have hSource : previous.1.1.2 ≤ BinaryCompleteRequestArithmeticEntryWork.pairCost next frame state+previous.1.1.2+BinaryBigEndian.littleValue previous.1.1.1.1.2.1+BinaryBigEndian.littleValue previous.1.1.1.1.2.2+usage previous.1.1.1.2+
      BinaryGenerationExecutionCharges.total previous.1.2+previous.2.1.1+previous.2.1.2+previous.2.2.1.1.1.1.1.1.1.1.1.1+previous.2.2.1.1.1.1.1.1.1.1.1.2+previous.2.2.1.1.1.1.1.1.1.1.2+previous.2.2.1.1.1.1.1.1.1.2+previous.2.2.1.1.1.1.1.1.2+previous.2.2.1.1.1.1.1.2+previous.2.2.1.1.1.1.2+previous.2.2.1.1.1.2+previous.2.2.1.1.2+previous.2.2.1.2+previous.2.2.2.1.1.1.1.1.1+previous.2.2.2.1.1.1.1.1.2+previous.2.2.2.1.1.1.1.2+previous.2.2.2.1.1.1.2+previous.2.2.2.1.1.2+previous.2.2.2.1.2+previous.2.2.2.2 := by
    simpa only [Nat.add_assoc] using
      (Nat.le_add_left previous.1.1.2 (BinaryCompleteRequestArithmeticEntryWork.pairCost next frame state)).trans
        (Nat.le_add_right (BinaryCompleteRequestArithmeticEntryWork.pairCost next frame state+previous.1.1.2) (BinaryBigEndian.littleValue previous.1.1.1.1.2.1 + BinaryBigEndian.littleValue previous.1.1.1.1.2.2 + usage previous.1.1.1.2 + 
      BinaryGenerationExecutionCharges.total previous.1.2 + previous.2.1.1 + previous.2.1.2 + previous.2.2.1.1.1.1.1.1.1.1.1.1 + previous.2.2.1.1.1.1.1.1.1.1.1.2 + previous.2.2.1.1.1.1.1.1.1.1.2 + previous.2.2.1.1.1.1.1.1.1.2 + previous.2.2.1.1.1.1.1.1.2 + previous.2.2.1.1.1.1.1.2 + previous.2.2.1.1.1.1.2 + previous.2.2.1.1.1.2 + previous.2.2.1.1.2 + previous.2.2.1.2 + previous.2.2.2.1.1.1.1.1.1 + previous.2.2.2.1.1.1.1.1.2 + previous.2.2.2.1.1.1.1.2 + previous.2.2.2.1.1.1.2 + previous.2.2.2.1.1.2 + previous.2.2.2.1.2 + previous.2.2.2.2))
  exact join_source_component previous.1.1.2 (BinaryCompleteRequestArithmeticEntryWork.pairCost next frame state+previous.1.1.2+BinaryBigEndian.littleValue previous.1.1.1.1.2.1+BinaryBigEndian.littleValue previous.1.1.1.1.2.2+usage previous.1.1.1.2+
      BinaryGenerationExecutionCharges.total previous.1.2+previous.2.1.1+previous.2.1.2+previous.2.2.1.1.1.1.1.1.1.1.1.1+previous.2.2.1.1.1.1.1.1.1.1.1.2+previous.2.2.1.1.1.1.1.1.1.1.2+previous.2.2.1.1.1.1.1.1.1.2+previous.2.2.1.1.1.1.1.1.2+previous.2.2.1.1.1.1.1.2+previous.2.2.1.1.1.1.2+previous.2.2.1.1.1.2+previous.2.2.1.1.2+previous.2.2.1.2+previous.2.2.2.1.1.1.1.1.1+previous.2.2.2.1.1.1.1.1.2+previous.2.2.2.1.1.1.1.2+previous.2.2.2.1.1.1.2+previous.2.2.2.1.1.2+previous.2.2.2.1.2+previous.2.2.2.2) extra (C*(frame.length+1)^d) hSource he ho


theorem parsedPair_complete_joint : ∃ C d : ℕ,∀ {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S),
    let returned := BinaryPromiseOpcodeRequest.parsedPairWithOutputExtras next frame state
    let produced := returned.1
    (BinaryCompleteRequestArithmeticEntryWork.parsedPairCost next frame state+produced.1.1.2+BinaryBigEndian.littleValue produced.1.1.1.1.2.1+BinaryBigEndian.littleValue produced.1.1.1.1.2.2+usage produced.1.1.1.2+
      BinaryGenerationExecutionCharges.total produced.1.2+produced.2.1.1+produced.2.1.2+produced.2.2.1.1.1.1.1.1.1.1.1.1+produced.2.2.1.1.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.2+produced.2.2.1.1.1.1.2+produced.2.2.1.1.1.2+produced.2.2.1.1.2+produced.2.2.1.2+produced.2.2.2.1.1.1.1.1.1+produced.2.2.2.1.1.1.1.1.2+produced.2.2.2.1.1.1.1.2+produced.2.2.2.1.1.1.2+produced.2.2.2.1.1.2+produced.2.2.2.1.2+produced.2.2.2.2)+returned.2 ≤ C*(frame.length+1)^d ∧
      binaryWordWidth returned.2 ≤ binaryWordWidth (C*(frame.length+1)^d) := by
  obtain ⟨C,d,hOld⟩ := BinaryCompleteRequestArithmeticEntryWork.parsedPair_complete_joint
  refine ⟨156*C,d,?_⟩
  intro S next frame state
  have ho := hOld next frame state
  have he := parsedPair_bound next frame state
  dsimp only at ho ⊢
  simp only [BinaryPromiseOpcodeRequest.parsedPairWithOutputExtras_compat,Nat.mul_assoc] at he ⊢
  generalize (BinaryPromiseOpcodeRequest.parsedPairWithOutputExtras next frame state).2 = extra at he ⊢
  generalize BinaryPromiseOpcodeRequest.parsedPair next frame state = previous at ho he ⊢
  have hSource : previous.1.1.2 ≤ BinaryCompleteRequestArithmeticEntryWork.parsedPairCost next frame state+previous.1.1.2+BinaryBigEndian.littleValue previous.1.1.1.1.2.1+BinaryBigEndian.littleValue previous.1.1.1.1.2.2+usage previous.1.1.1.2+
      BinaryGenerationExecutionCharges.total previous.1.2+previous.2.1.1+previous.2.1.2+previous.2.2.1.1.1.1.1.1.1.1.1.1+previous.2.2.1.1.1.1.1.1.1.1.1.2+previous.2.2.1.1.1.1.1.1.1.1.2+previous.2.2.1.1.1.1.1.1.1.2+previous.2.2.1.1.1.1.1.1.2+previous.2.2.1.1.1.1.1.2+previous.2.2.1.1.1.1.2+previous.2.2.1.1.1.2+previous.2.2.1.1.2+previous.2.2.1.2+previous.2.2.2.1.1.1.1.1.1+previous.2.2.2.1.1.1.1.1.2+previous.2.2.2.1.1.1.1.2+previous.2.2.2.1.1.1.2+previous.2.2.2.1.1.2+previous.2.2.2.1.2+previous.2.2.2.2 := by
    simpa only [Nat.add_assoc] using
      (Nat.le_add_left previous.1.1.2 (BinaryCompleteRequestArithmeticEntryWork.parsedPairCost next frame state)).trans
        (Nat.le_add_right (BinaryCompleteRequestArithmeticEntryWork.parsedPairCost next frame state+previous.1.1.2) (BinaryBigEndian.littleValue previous.1.1.1.1.2.1 + BinaryBigEndian.littleValue previous.1.1.1.1.2.2 + usage previous.1.1.1.2 + 
      BinaryGenerationExecutionCharges.total previous.1.2 + previous.2.1.1 + previous.2.1.2 + previous.2.2.1.1.1.1.1.1.1.1.1.1 + previous.2.2.1.1.1.1.1.1.1.1.1.2 + previous.2.2.1.1.1.1.1.1.1.1.2 + previous.2.2.1.1.1.1.1.1.1.2 + previous.2.2.1.1.1.1.1.1.2 + previous.2.2.1.1.1.1.1.2 + previous.2.2.1.1.1.1.2 + previous.2.2.1.1.1.2 + previous.2.2.1.1.2 + previous.2.2.1.2 + previous.2.2.2.1.1.1.1.1.1 + previous.2.2.2.1.1.1.1.1.2 + previous.2.2.2.1.1.1.1.2 + previous.2.2.2.1.1.1.2 + previous.2.2.2.1.1.2 + previous.2.2.2.1.2 + previous.2.2.2.2))
  exact join_source_component previous.1.1.2 (BinaryCompleteRequestArithmeticEntryWork.parsedPairCost next frame state+previous.1.1.2+BinaryBigEndian.littleValue previous.1.1.1.1.2.1+BinaryBigEndian.littleValue previous.1.1.1.1.2.2+usage previous.1.1.1.2+
      BinaryGenerationExecutionCharges.total previous.1.2+previous.2.1.1+previous.2.1.2+previous.2.2.1.1.1.1.1.1.1.1.1.1+previous.2.2.1.1.1.1.1.1.1.1.1.2+previous.2.2.1.1.1.1.1.1.1.1.2+previous.2.2.1.1.1.1.1.1.1.2+previous.2.2.1.1.1.1.1.1.2+previous.2.2.1.1.1.1.1.2+previous.2.2.1.1.1.1.2+previous.2.2.1.1.1.2+previous.2.2.1.1.2+previous.2.2.1.2+previous.2.2.2.1.1.1.1.1.1+previous.2.2.2.1.1.1.1.1.2+previous.2.2.2.1.1.1.1.2+previous.2.2.2.1.1.1.2+previous.2.2.2.1.1.2+previous.2.2.2.1.2+previous.2.2.2.2) extra (C*(frame.length+1)^d) hSource he ho

end Blotto.BinaryReturnedOutputExtras
