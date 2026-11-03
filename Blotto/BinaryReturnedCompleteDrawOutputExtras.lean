import Blotto.BinaryReturnedOutputExtras
import Blotto.BinaryReturnedTerminalDrawExtras

/-! Joint returned draw/output normalization fields through all six actual
complete interfaces. Old output extras and full records are preserved. Other
normalization callers and full native/physical models remain separate. -/
namespace Blotto.BinaryReturnedCompleteDrawOutputExtras
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryTerminalPhysicalAllowanceCache (Parsed)
open BinaryPRGResourceWork BinaryPRGTerminalWork BinaryCachedGroupInputHeight BinaryTerminalCacheCertificate
open BinaryReturnedOutputExtras (join_source_component)
set_option autoImplicit false
set_option maxHeartbeats 4000000
attribute [local irreducible] BinaryNormalizedCoordinate.opcode

theorem draw_bound {E : Type*} [Zero E] [Add E] (backend : BinaryCacheContinuationCore.Backend E) (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) :
    (BinaryCacheContinuationCore.drawWithDrawExtras backend frame parsed hParsed seed rich K outer scalar).2 ≤155*(BinaryCacheContinuationCore.drawWithDrawExtras backend frame parsed hParsed seed rich K outer scalar).1.1.1.2 := by
  let request := parsed.1.2.logical.request
  let child := BinaryCacheContinuationCore.certified backend frame parsed hParsed seed rich
  let returned := child.1
  let observed := returned.1
  simp only [BinaryCacheContinuationCore.drawWithDrawExtras_record]
  split
  · dsimp only; omega
  · rename_i result hs
    have h := BinaryReturnedTerminalDrawExtras.terminal_bound seed result.2
          (terminal_canonical request rich result.1)
          (BinaryPRGHeapCertifiedPrefixProperties.admissible seed request rich result
            (BinaryTerminalPhysicalAllowanceDraw.logical_success frame parsed hParsed seed rich result
              (by simpa only [observed,returned,child,BinaryCacheContinuationCore.certified_compat,BinaryTerminalPhysicalAllowanceCertified.run] using hs)))
          K outer scalar observed.1.1.1.2 (by simpa only [observed,returned,child,BinaryCacheContinuationCore.certified_compat,BinaryTerminalPhysicalAllowanceCertified.run] using
            (BinaryTerminalPhysicalAllowanceDraw.cursor_bound frame parsed hParsed seed rich))
    dsimp only [request,observed,returned,child] at h
    dsimp only
    omega

theorem fixed_bound {E : Type*} [Zero E] [Add E] (backend : BinaryCacheContinuationCore.Backend E) (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) :
    (BinaryCacheContinuationCore.fixedWithDrawExtras backend frame parsed hParsed seed rich K outer scalar).2 ≤155*(BinaryCacheContinuationCore.fixedWithDrawExtras backend frame parsed hParsed seed rich K outer scalar).1.1.1.2 := by
  have h := draw_bound backend frame parsed hParsed seed rich K outer scalar
  simp only [BinaryCacheContinuationCore.fixedWithDrawExtras_record]
  split <;> dsimp only <;> omega

theorem framed_bound {E : Type*} [Zero E] [Add E] (backend : BinaryCacheContinuationCore.Backend E)
    (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (header : BinaryPRGHeaderFrame.Header parsed.1.1) :
    ((BinaryCacheContinuationCore.framedWithDrawOutputExtras backend frame parsed hParsed seed rich K outer scalar header).1.2+(BinaryCacheContinuationCore.framedWithDrawOutputExtras backend frame parsed hParsed seed rich K outer scalar header).2) ≤
      155*(BinaryCacheContinuationCore.framedWithDrawOutputExtras backend frame parsed hParsed seed rich K outer scalar header).1.1.1.1.2 := by
  let supplied := BinaryCacheContinuationCore.fixedWithDrawExtras backend frame parsed hParsed seed rich K outer scalar
  let child := supplied.1
  let returned := child.1
  let drawn := returned.1
  have hd := fixed_bound backend frame parsed hParsed seed rich K outer scalar
  have ho := BinaryReturnedOutputExtras.output_bound parsed.1.2.logical.request.prepared.original.a header.bytes drawn.1.1.1.1.data.toList
  dsimp only [drawn,returned,child,supplied] at ho
  simp only [BinaryCacheContinuationCore.framedWithDrawOutputExtras_record]
  omega


theorem seed_bound {E : Type*} [Zero E] [Add E] (backend : BinaryCacheContinuationCore.Backend E)
    (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (bits : List Bool) :
    ((BinaryCacheContinuationCore.seedWithDrawOutputExtras backend frame parsed hParsed rich bits).1.2+(BinaryCacheContinuationCore.seedWithDrawOutputExtras backend frame parsed hParsed rich bits).2) ≤
      155*(BinaryCacheContinuationCore.seedWithDrawOutputExtras backend frame parsed hParsed rich bits).1.1.1.1.2 := by
  simp only [BinaryCacheContinuationCore.seedWithDrawOutputExtras_record]
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
    ((BinaryCacheFinishRequest.seedWithDrawOutputExtras frame parsed hParsed rich bits).1.2+(BinaryCacheFinishRequest.seedWithDrawOutputExtras frame parsed hParsed rich bits).2) ≤
      155*(BinaryCacheFinishRequest.seedWithDrawOutputExtras frame parsed hParsed rich bits).1.1.1.1.2 :=
  seed_bound BinaryCacheFinishRequest.backend frame parsed hParsed rich bits

theorem parser_raw_bound {E : Type*} [Zero E] [Add E] (backend : BinaryRawParserContinuation.Backend E) (rich : Bool) (frame bits : List Bool) :
    ((BinaryRawParserContinuation.rawWithDrawOutputExtras backend rich frame bits).1.2+(BinaryRawParserContinuation.rawWithDrawOutputExtras backend rich frame bits).2) ≤ 155*(BinaryRawParserContinuation.rawWithDrawOutputExtras backend rich frame bits).1.1.1.1.2 := by
  simp only [BinaryRawParserContinuation.rawWithDrawOutputExtras_record]
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
    ((BinaryRawParserContinuation.parsedRawWithDrawOutputExtras backend rich frame bits).1.2+(BinaryRawParserContinuation.parsedRawWithDrawOutputExtras backend rich frame bits).2) ≤ 155*(BinaryRawParserContinuation.parsedRawWithDrawOutputExtras backend rich frame bits).1.1.1.1.2 := by
  simp only [BinaryRawParserContinuation.parsedRawWithDrawOutputExtras_record]
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
    ((BinaryRawParserContinuation.generatedWithDrawOutputExtras backend next rich frame state).1.2+(BinaryRawParserContinuation.generatedWithDrawOutputExtras backend next rich frame state).2) ≤ 155*(BinaryRawParserContinuation.generatedWithDrawOutputExtras backend next rich frame state).1.1.1.1.2 := by
  simp only [BinaryRawParserContinuation.generatedWithDrawOutputExtras_record]
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
    ((BinaryRawParserContinuation.parsedGeneratedWithDrawOutputExtras backend next rich frame state).1.2+(BinaryRawParserContinuation.parsedGeneratedWithDrawOutputExtras backend next rich frame state).2) ≤ 155*(BinaryRawParserContinuation.parsedGeneratedWithDrawOutputExtras backend next rich frame state).1.1.1.1.2 := by
  simp only [BinaryRawParserContinuation.parsedGeneratedWithDrawOutputExtras_record]
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
    ((BinaryRawParserContinuation.pairWithDrawOutputExtras backend next frame state).1.2+(BinaryRawParserContinuation.pairWithDrawOutputExtras backend next frame state).2) ≤ 155*(BinaryRawParserContinuation.pairWithDrawOutputExtras backend next frame state).1.1.1.1.2 := by
  let first := BinaryRawParserContinuation.generatedWithDrawOutputExtras backend next true frame state
  let rich := first.1.1.1
  have hFirst := parser_generated_bound backend next true frame state
  have hSecond := parser_generated_bound backend next false frame rich.1.1.1.1.2
  dsimp only [rich,first] at hSecond
  simp only [BinaryRawParserContinuation.pairWithDrawOutputExtras_record]
  omega

theorem parser_parsedPair_bound {E : Type*} [Zero E] [Add E] (backend : BinaryRawParserContinuation.Backend E)
    {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    ((BinaryRawParserContinuation.parsedPairWithDrawOutputExtras backend next frame state).1.2+(BinaryRawParserContinuation.parsedPairWithDrawOutputExtras backend next frame state).2) ≤ 155*(BinaryRawParserContinuation.parsedPairWithDrawOutputExtras backend next frame state).1.1.1.1.2 := by
  let first := BinaryRawParserContinuation.parsedGeneratedWithDrawOutputExtras backend next true frame state
  let rich := first.1.1.1
  have hFirst := parser_parsedGenerated_bound backend next true frame state
  have hSecond := parser_parsedGenerated_bound backend next false frame rich.1.1.1.1.2
  dsimp only [rich,first] at hSecond
  simp only [BinaryRawParserContinuation.parsedPairWithDrawOutputExtras_record]
  omega

theorem raw_bound (rich : Bool) (frame bits : List Bool) :
    ((BinaryPromiseOpcodeRequest.rawWithDrawOutputExtras rich frame bits).1.2+(BinaryPromiseOpcodeRequest.rawWithDrawOutputExtras rich frame bits).2) ≤ 155*(BinaryPromiseOpcodeRequest.rawWithDrawOutputExtras rich frame bits).1.1.1.1.2 :=
  parser_raw_bound BinaryPromiseOpcodeRequest.backend rich frame bits

theorem parsedRaw_bound (rich : Bool) (frame bits : List Bool) :
    ((BinaryPromiseOpcodeRequest.parsedRawWithDrawOutputExtras rich frame bits).1.2+(BinaryPromiseOpcodeRequest.parsedRawWithDrawOutputExtras rich frame bits).2) ≤ 155*(BinaryPromiseOpcodeRequest.parsedRawWithDrawOutputExtras rich frame bits).1.1.1.1.2 :=
  parser_parsedRaw_bound BinaryPromiseOpcodeRequest.backend rich frame bits

theorem generated_bound {S : Type*} (next : S → Bool × S) (rich : Bool) (frame : List Bool) (state : S) :
    ((BinaryPromiseOpcodeRequest.generatedWithDrawOutputExtras next rich frame state).1.2+(BinaryPromiseOpcodeRequest.generatedWithDrawOutputExtras next rich frame state).2) ≤ 155*(BinaryPromiseOpcodeRequest.generatedWithDrawOutputExtras next rich frame state).1.1.1.1.2 :=
  parser_generated_bound BinaryPromiseOpcodeRequest.backend next rich frame state

theorem parsedGenerated_bound {S : Type*} (next : S → Bool × S) (rich : Bool) (frame : List Bool) (state : S) :
    ((BinaryPromiseOpcodeRequest.parsedGeneratedWithDrawOutputExtras next rich frame state).1.2+(BinaryPromiseOpcodeRequest.parsedGeneratedWithDrawOutputExtras next rich frame state).2) ≤ 155*(BinaryPromiseOpcodeRequest.parsedGeneratedWithDrawOutputExtras next rich frame state).1.1.1.1.2 :=
  parser_parsedGenerated_bound BinaryPromiseOpcodeRequest.backend next rich frame state

theorem pair_bound {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    ((BinaryPromiseOpcodeRequest.pairWithDrawOutputExtras next frame state).1.2+(BinaryPromiseOpcodeRequest.pairWithDrawOutputExtras next frame state).2) ≤ 155*(BinaryPromiseOpcodeRequest.pairWithDrawOutputExtras next frame state).1.1.1.1.2 :=
  parser_pair_bound BinaryPromiseOpcodeRequest.backend next frame state

theorem parsedPair_bound {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    ((BinaryPromiseOpcodeRequest.parsedPairWithDrawOutputExtras next frame state).1.2+(BinaryPromiseOpcodeRequest.parsedPairWithDrawOutputExtras next frame state).2) ≤ 155*(BinaryPromiseOpcodeRequest.parsedPairWithDrawOutputExtras next frame state).1.1.1.1.2 :=
  parser_parsedPair_bound BinaryPromiseOpcodeRequest.backend next frame state

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
attribute [local irreducible]
  BinaryPromiseOpcodeRequest.rawWithDrawOutputExtras
  BinaryPromiseOpcodeRequest.parsedRawWithDrawOutputExtras
  BinaryPromiseOpcodeRequest.generatedWithDrawOutputExtras
  BinaryPromiseOpcodeRequest.parsedGeneratedWithDrawOutputExtras
  BinaryPromiseOpcodeRequest.pairWithDrawOutputExtras
  BinaryPromiseOpcodeRequest.parsedPairWithDrawOutputExtras
attribute [local irreducible] BinaryPRGHeapTraceUsage.usage BinarySamplerExecutionCharges.total
  BinaryGenerationExecutionCharges.total BinaryBigEndian.littleValue
set_option maxHeartbeats 300000

theorem raw_complete_joint : ∃ C d : ℕ,∀ (rich : Bool) (frame bits : List Bool),
    let returned := BinaryPromiseOpcodeRequest.rawWithDrawOutputExtras rich frame bits
    let produced := returned.1.1
    (BinaryCompleteRequestArithmeticEntryWork.rawCost rich frame bits+produced.1.1.2+BinaryBigEndian.littleValue produced.1.1.1.1.2+usage produced.1.1.1.2+
      BinarySamplerExecutionCharges.total produced.1.2+produced.2.1.1+produced.2.1.2+produced.2.2.1.1.1.1.1.1.1.1.1.1+produced.2.2.1.1.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.2+produced.2.2.1.1.1.1.2+produced.2.2.1.1.1.2+produced.2.2.1.1.2+produced.2.2.1.2+produced.2.2.2.1.1.1.1.1.1+produced.2.2.2.1.1.1.1.1.2+produced.2.2.2.1.1.1.1.2+produced.2.2.2.1.1.1.2+produced.2.2.2.1.1.2+produced.2.2.2.1.2+produced.2.2.2.2)+(returned.1.2+returned.2) ≤ C*(frame.length+1)^d ∧
      binaryWordWidth (returned.1.2+returned.2) ≤ binaryWordWidth (C*(frame.length+1)^d) := by
  obtain ⟨C,d,hOld⟩ := BinaryCompleteRequestArithmeticEntryWork.raw_complete_joint
  refine ⟨156*C,d,?_⟩
  intro rich frame bits
  have ho := hOld rich frame bits
  have he := raw_bound rich frame bits
  dsimp only at ho ⊢
  simp only [BinaryPromiseOpcodeRequest.rawWithDrawOutputExtras_compat,BinaryPromiseOpcodeRequest.rawWithOutputExtras_compat,Nat.mul_assoc] at he ⊢
  generalize (BinaryPromiseOpcodeRequest.rawWithOutputExtras rich frame bits).2+(BinaryPromiseOpcodeRequest.rawWithDrawOutputExtras rich frame bits).2 = extra at he ⊢
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
    let returned := BinaryPromiseOpcodeRequest.parsedRawWithDrawOutputExtras rich frame bits
    let produced := returned.1.1
    (BinaryCompleteRequestArithmeticEntryWork.rawCost rich frame bits+produced.1.1.2+BinaryBigEndian.littleValue produced.1.1.1.1.2+usage produced.1.1.1.2+
      BinarySamplerExecutionCharges.total produced.1.2+produced.2.1.1+produced.2.1.2+produced.2.2.1.1.1.1.1.1.1.1.1.1+produced.2.2.1.1.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.2+produced.2.2.1.1.1.1.2+produced.2.2.1.1.1.2+produced.2.2.1.1.2+produced.2.2.1.2+produced.2.2.2.1.1.1.1.1.1+produced.2.2.2.1.1.1.1.1.2+produced.2.2.2.1.1.1.1.2+produced.2.2.2.1.1.1.2+produced.2.2.2.1.1.2+produced.2.2.2.1.2+produced.2.2.2.2)+(returned.1.2+returned.2) ≤ C*(frame.length+1)^d ∧
      binaryWordWidth (returned.1.2+returned.2) ≤ binaryWordWidth (C*(frame.length+1)^d) := by
  obtain ⟨C,d,hOld⟩ := BinaryCompleteRequestArithmeticEntryWork.parsedRaw_complete_joint
  refine ⟨156*C,d,?_⟩
  intro rich frame bits
  have ho := hOld rich frame bits
  have he := parsedRaw_bound rich frame bits
  dsimp only at ho ⊢
  simp only [BinaryPromiseOpcodeRequest.parsedRawWithDrawOutputExtras_compat,BinaryPromiseOpcodeRequest.parsedRawWithOutputExtras_compat,Nat.mul_assoc] at he ⊢
  generalize (BinaryPromiseOpcodeRequest.parsedRawWithOutputExtras rich frame bits).2+(BinaryPromiseOpcodeRequest.parsedRawWithDrawOutputExtras rich frame bits).2 = extra at he ⊢
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
    let returned := BinaryPromiseOpcodeRequest.generatedWithDrawOutputExtras next rich frame state
    let produced := returned.1.1
    (BinaryCompleteRequestArithmeticEntryWork.generatedCost next rich frame state+produced.1.1.2+BinaryBigEndian.littleValue produced.1.1.1.1.2+usage produced.1.1.1.2+
      BinaryGenerationExecutionCharges.total produced.1.2+produced.2.1.1+produced.2.1.2+produced.2.2.1.1.1.1.1.1.1.1.1.1+produced.2.2.1.1.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.2+produced.2.2.1.1.1.1.2+produced.2.2.1.1.1.2+produced.2.2.1.1.2+produced.2.2.1.2+produced.2.2.2.1.1.1.1.1.1+produced.2.2.2.1.1.1.1.1.2+produced.2.2.2.1.1.1.1.2+produced.2.2.2.1.1.1.2+produced.2.2.2.1.1.2+produced.2.2.2.1.2+produced.2.2.2.2)+(returned.1.2+returned.2) ≤ C*(frame.length+1)^d ∧
      binaryWordWidth (returned.1.2+returned.2) ≤ binaryWordWidth (C*(frame.length+1)^d) := by
  obtain ⟨C,d,hOld⟩ := BinaryCompleteRequestArithmeticEntryWork.generated_complete_joint
  refine ⟨156*C,d,?_⟩
  intro S next rich frame state
  have ho := hOld next rich frame state
  have he := generated_bound next rich frame state
  dsimp only at ho ⊢
  simp only [BinaryPromiseOpcodeRequest.generatedWithDrawOutputExtras_compat,BinaryPromiseOpcodeRequest.generatedWithOutputExtras_compat,Nat.mul_assoc] at he ⊢
  generalize (BinaryPromiseOpcodeRequest.generatedWithOutputExtras next rich frame state).2+(BinaryPromiseOpcodeRequest.generatedWithDrawOutputExtras next rich frame state).2 = extra at he ⊢
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
    let returned := BinaryPromiseOpcodeRequest.parsedGeneratedWithDrawOutputExtras next rich frame state
    let produced := returned.1.1
    (BinaryCompleteRequestArithmeticEntryWork.generatedCost next rich frame state+produced.1.1.2+BinaryBigEndian.littleValue produced.1.1.1.1.2+usage produced.1.1.1.2+
      BinaryGenerationExecutionCharges.total produced.1.2+produced.2.1.1+produced.2.1.2+produced.2.2.1.1.1.1.1.1.1.1.1.1+produced.2.2.1.1.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.2+produced.2.2.1.1.1.1.2+produced.2.2.1.1.1.2+produced.2.2.1.1.2+produced.2.2.1.2+produced.2.2.2.1.1.1.1.1.1+produced.2.2.2.1.1.1.1.1.2+produced.2.2.2.1.1.1.1.2+produced.2.2.2.1.1.1.2+produced.2.2.2.1.1.2+produced.2.2.2.1.2+produced.2.2.2.2)+(returned.1.2+returned.2) ≤ C*(frame.length+1)^d ∧
      binaryWordWidth (returned.1.2+returned.2) ≤ binaryWordWidth (C*(frame.length+1)^d) := by
  obtain ⟨C,d,hOld⟩ := BinaryCompleteRequestArithmeticEntryWork.parsedGenerated_complete_joint
  refine ⟨156*C,d,?_⟩
  intro S next rich frame state
  have ho := hOld next rich frame state
  have he := parsedGenerated_bound next rich frame state
  dsimp only at ho ⊢
  simp only [BinaryPromiseOpcodeRequest.parsedGeneratedWithDrawOutputExtras_compat,BinaryPromiseOpcodeRequest.parsedGeneratedWithOutputExtras_compat,Nat.mul_assoc] at he ⊢
  generalize (BinaryPromiseOpcodeRequest.parsedGeneratedWithOutputExtras next rich frame state).2+(BinaryPromiseOpcodeRequest.parsedGeneratedWithDrawOutputExtras next rich frame state).2 = extra at he ⊢
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
    let returned := BinaryPromiseOpcodeRequest.pairWithDrawOutputExtras next frame state
    let produced := returned.1.1
    (BinaryCompleteRequestArithmeticEntryWork.pairCost next frame state+produced.1.1.2+BinaryBigEndian.littleValue produced.1.1.1.1.2.1+BinaryBigEndian.littleValue produced.1.1.1.1.2.2+usage produced.1.1.1.2+
      BinaryGenerationExecutionCharges.total produced.1.2+produced.2.1.1+produced.2.1.2+produced.2.2.1.1.1.1.1.1.1.1.1.1+produced.2.2.1.1.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.2+produced.2.2.1.1.1.1.2+produced.2.2.1.1.1.2+produced.2.2.1.1.2+produced.2.2.1.2+produced.2.2.2.1.1.1.1.1.1+produced.2.2.2.1.1.1.1.1.2+produced.2.2.2.1.1.1.1.2+produced.2.2.2.1.1.1.2+produced.2.2.2.1.1.2+produced.2.2.2.1.2+produced.2.2.2.2)+(returned.1.2+returned.2) ≤ C*(frame.length+1)^d ∧
      binaryWordWidth (returned.1.2+returned.2) ≤ binaryWordWidth (C*(frame.length+1)^d) := by
  obtain ⟨C,d,hOld⟩ := BinaryCompleteRequestArithmeticEntryWork.pair_complete_joint
  refine ⟨156*C,d,?_⟩
  intro S next frame state
  have ho := hOld next frame state
  have he := pair_bound next frame state
  dsimp only at ho ⊢
  simp only [BinaryPromiseOpcodeRequest.pairWithDrawOutputExtras_compat,BinaryPromiseOpcodeRequest.pairWithOutputExtras_compat,Nat.mul_assoc] at he ⊢
  generalize (BinaryPromiseOpcodeRequest.pairWithOutputExtras next frame state).2+(BinaryPromiseOpcodeRequest.pairWithDrawOutputExtras next frame state).2 = extra at he ⊢
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
    let returned := BinaryPromiseOpcodeRequest.parsedPairWithDrawOutputExtras next frame state
    let produced := returned.1.1
    (BinaryCompleteRequestArithmeticEntryWork.parsedPairCost next frame state+produced.1.1.2+BinaryBigEndian.littleValue produced.1.1.1.1.2.1+BinaryBigEndian.littleValue produced.1.1.1.1.2.2+usage produced.1.1.1.2+
      BinaryGenerationExecutionCharges.total produced.1.2+produced.2.1.1+produced.2.1.2+produced.2.2.1.1.1.1.1.1.1.1.1.1+produced.2.2.1.1.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.2+produced.2.2.1.1.1.1.2+produced.2.2.1.1.1.2+produced.2.2.1.1.2+produced.2.2.1.2+produced.2.2.2.1.1.1.1.1.1+produced.2.2.2.1.1.1.1.1.2+produced.2.2.2.1.1.1.1.2+produced.2.2.2.1.1.1.2+produced.2.2.2.1.1.2+produced.2.2.2.1.2+produced.2.2.2.2)+(returned.1.2+returned.2) ≤ C*(frame.length+1)^d ∧
      binaryWordWidth (returned.1.2+returned.2) ≤ binaryWordWidth (C*(frame.length+1)^d) := by
  obtain ⟨C,d,hOld⟩ := BinaryCompleteRequestArithmeticEntryWork.parsedPair_complete_joint
  refine ⟨156*C,d,?_⟩
  intro S next frame state
  have ho := hOld next frame state
  have he := parsedPair_bound next frame state
  dsimp only at ho ⊢
  simp only [BinaryPromiseOpcodeRequest.parsedPairWithDrawOutputExtras_compat,BinaryPromiseOpcodeRequest.parsedPairWithOutputExtras_compat,Nat.mul_assoc] at he ⊢
  generalize (BinaryPromiseOpcodeRequest.parsedPairWithOutputExtras next frame state).2+(BinaryPromiseOpcodeRequest.parsedPairWithDrawOutputExtras next frame state).2 = extra at he ⊢
  generalize BinaryPromiseOpcodeRequest.parsedPair next frame state = previous at ho he ⊢
  have hSource : previous.1.1.2 ≤ BinaryCompleteRequestArithmeticEntryWork.parsedPairCost next frame state+previous.1.1.2+BinaryBigEndian.littleValue previous.1.1.1.1.2.1+BinaryBigEndian.littleValue previous.1.1.1.1.2.2+usage previous.1.1.1.2+
      BinaryGenerationExecutionCharges.total previous.1.2+previous.2.1.1+previous.2.1.2+previous.2.2.1.1.1.1.1.1.1.1.1.1+previous.2.2.1.1.1.1.1.1.1.1.1.2+previous.2.2.1.1.1.1.1.1.1.1.2+previous.2.2.1.1.1.1.1.1.1.2+previous.2.2.1.1.1.1.1.1.2+previous.2.2.1.1.1.1.1.2+previous.2.2.1.1.1.1.2+previous.2.2.1.1.1.2+previous.2.2.1.1.2+previous.2.2.1.2+previous.2.2.2.1.1.1.1.1.1+previous.2.2.2.1.1.1.1.1.2+previous.2.2.2.1.1.1.1.2+previous.2.2.2.1.1.1.2+previous.2.2.2.1.1.2+previous.2.2.2.1.2+previous.2.2.2.2 := by
    simpa only [Nat.add_assoc] using
      (Nat.le_add_left previous.1.1.2 (BinaryCompleteRequestArithmeticEntryWork.parsedPairCost next frame state)).trans
        (Nat.le_add_right (BinaryCompleteRequestArithmeticEntryWork.parsedPairCost next frame state+previous.1.1.2) (BinaryBigEndian.littleValue previous.1.1.1.1.2.1 + BinaryBigEndian.littleValue previous.1.1.1.1.2.2 + usage previous.1.1.1.2 + 
      BinaryGenerationExecutionCharges.total previous.1.2 + previous.2.1.1 + previous.2.1.2 + previous.2.2.1.1.1.1.1.1.1.1.1.1 + previous.2.2.1.1.1.1.1.1.1.1.1.2 + previous.2.2.1.1.1.1.1.1.1.1.2 + previous.2.2.1.1.1.1.1.1.1.2 + previous.2.2.1.1.1.1.1.1.2 + previous.2.2.1.1.1.1.1.2 + previous.2.2.1.1.1.1.2 + previous.2.2.1.1.1.2 + previous.2.2.1.1.2 + previous.2.2.1.2 + previous.2.2.2.1.1.1.1.1.1 + previous.2.2.2.1.1.1.1.1.2 + previous.2.2.2.1.1.1.1.2 + previous.2.2.2.1.1.1.2 + previous.2.2.2.1.1.2 + previous.2.2.2.1.2 + previous.2.2.2.2))
  exact join_source_component previous.1.1.2 (BinaryCompleteRequestArithmeticEntryWork.parsedPairCost next frame state+previous.1.1.2+BinaryBigEndian.littleValue previous.1.1.1.1.2.1+BinaryBigEndian.littleValue previous.1.1.1.1.2.2+usage previous.1.1.1.2+
      BinaryGenerationExecutionCharges.total previous.1.2+previous.2.1.1+previous.2.1.2+previous.2.2.1.1.1.1.1.1.1.1.1.1+previous.2.2.1.1.1.1.1.1.1.1.1.2+previous.2.2.1.1.1.1.1.1.1.1.2+previous.2.2.1.1.1.1.1.1.1.2+previous.2.2.1.1.1.1.1.1.2+previous.2.2.1.1.1.1.1.2+previous.2.2.1.1.1.1.2+previous.2.2.1.1.1.2+previous.2.2.1.1.2+previous.2.2.1.2+previous.2.2.2.1.1.1.1.1.1+previous.2.2.2.1.1.1.1.1.2+previous.2.2.2.1.1.1.1.2+previous.2.2.2.1.1.1.2+previous.2.2.2.1.1.2+previous.2.2.2.1.2+previous.2.2.2.2) extra (C*(frame.length+1)^d) hSource he ho

end Blotto.BinaryReturnedCompleteDrawOutputExtras
