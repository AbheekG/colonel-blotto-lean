import Blotto.BinaryReturnedFactoryExtras

/-! The final actually emitted trace pays for every array header, including
zero-slot arrays. These are trace/source bounds and do not choose native
representation prices or interpret host allocation. -/
namespace Blotto.BinaryCompleteTraceHeaders
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryTerminalPhysicalAllowanceCache (Parsed)
set_option autoImplicit false
set_option maxHeartbeats 1500000

theorem arrayRecords_le_length (trace : Trace) : arrayRecords trace ≤ trace.length := by
  induction trace with
  | nil => rfl
  | cons event rest ih => cases event <;> simp only [arrayRecords,List.length_cons] <;> omega

theorem one_length_le (slots frames : ℕ) (trace : Trace) :
    (BinaryWrapperEmission.one slots frames trace).1.length ≤ (BinaryWrapperEmission.one slots frames trace).2 := by
  rw [BinaryWrapperEmission.one_length,BinaryWrapperEmission.one_work]
  omega

theorem two_length_le (slots frames : ℕ) (first second : Trace) :
    (BinaryWrapperEmission.two slots frames first second).1.length ≤ (BinaryWrapperEmission.two slots frames first second).2 := by
  rw [BinaryWrapperEmission.two_length,BinaryWrapperEmission.two_work]
  omega

theorem three_length_le (slots frames : ℕ) (first second third : Trace) :
    (BinarySeedWrapperEmission.three slots frames first second third).1.length ≤ (BinarySeedWrapperEmission.three slots frames first second third).2 := by
  rw [BinarySeedWrapperEmission.three_length,BinarySeedWrapperEmission.three_work]
  omega

attribute [local irreducible] BinaryCacheFinishRequest.seedWithFactoryExtras BinaryRawParserContinuation.rawWithFactoryExtras BinaryRawParserContinuation.parsedRawWithFactoryExtras BinaryRawParserContinuation.generatedWithFactoryExtras BinaryRawParserContinuation.parsedGeneratedWithFactoryExtras BinaryRawParserContinuation.pairWithFactoryExtras BinaryRawParserContinuation.parsedPairWithFactoryExtras

theorem parser_raw_length {E : Type*} [Zero E] [Add E] (backend : BinaryRawParserContinuation.Backend E) (rich : Bool) (frame bits : List Bool) :
    let produced := (BinaryRawParserContinuation.rawWithFactoryExtras backend rich frame bits).1.1.1.1.1
    produced.1.1.1.2.length ≤ BinarySamplerExecutionCharges.total produced.1.2 := by
  simp only [BinaryRawParserContinuation.rawWithFactoryExtras]
  split
  · simp only [BinarySamplerExecutionCharges.total_addWrapper,BinarySamplerExecutionCharges.total_zero,BinaryWrapperEmission.one_length,BinaryWrapperEmission.one_work,BinaryWrapperEmission.two_length,BinaryWrapperEmission.two_work,BinarySeedWrapperEmission.three_length,BinarySeedWrapperEmission.three_work]
    omega
  · split
    · simp only [BinarySamplerExecutionCharges.total_addWrapper,BinarySamplerExecutionCharges.total_zero,BinaryWrapperEmission.one_length,BinaryWrapperEmission.one_work,BinaryWrapperEmission.two_length,BinaryWrapperEmission.two_work,BinarySeedWrapperEmission.three_length,BinarySeedWrapperEmission.three_work]
      omega
    · simp only [BinarySamplerExecutionCharges.total_addWrapper,BinarySamplerExecutionCharges.total_zero,BinaryWrapperEmission.one_length,BinaryWrapperEmission.one_work,BinaryWrapperEmission.two_length,BinaryWrapperEmission.two_work,BinarySeedWrapperEmission.three_length,BinarySeedWrapperEmission.three_work]
      omega

theorem parser_parsedRaw_length {E : Type*} [Zero E] [Add E] (backend : BinaryRawParserContinuation.Backend E) (rich : Bool) (frame bits : List Bool) :
    let produced := (BinaryRawParserContinuation.parsedRawWithFactoryExtras backend rich frame bits).1.1.1.1.1
    produced.1.1.1.2.length ≤ BinarySamplerExecutionCharges.total produced.1.2 := by
  simp only [BinaryRawParserContinuation.parsedRawWithFactoryExtras]
  split
  · simp only [BinarySamplerExecutionCharges.total_addWrapper,BinarySamplerExecutionCharges.total_zero,BinaryWrapperEmission.one_length,BinaryWrapperEmission.one_work,BinaryWrapperEmission.two_length,BinaryWrapperEmission.two_work,BinarySeedWrapperEmission.three_length,BinarySeedWrapperEmission.three_work]
    omega
  · split
    · simp only [BinarySamplerExecutionCharges.total_addWrapper,BinarySamplerExecutionCharges.total_zero,BinaryWrapperEmission.one_length,BinaryWrapperEmission.one_work,BinaryWrapperEmission.two_length,BinaryWrapperEmission.two_work,BinarySeedWrapperEmission.three_length,BinarySeedWrapperEmission.three_work]
      omega
    · simp only [BinarySamplerExecutionCharges.total_addWrapper,BinarySamplerExecutionCharges.total_zero,BinaryWrapperEmission.one_length,BinaryWrapperEmission.one_work,BinaryWrapperEmission.two_length,BinaryWrapperEmission.two_work,BinarySeedWrapperEmission.three_length,BinarySeedWrapperEmission.three_work]
      omega

theorem parser_generated_length {E : Type*} [Zero E] [Add E] (backend : BinaryRawParserContinuation.Backend E) {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) :
    let produced := (BinaryRawParserContinuation.generatedWithFactoryExtras backend next rich frame state).1.1.1.1.1
    produced.1.1.1.2.length ≤ BinaryGenerationExecutionCharges.total produced.1.2 := by
  simp only [BinaryRawParserContinuation.generatedWithFactoryExtras]
  split
  · simp only [BinaryGenerationExecutionCharges.total_addWrapper,BinaryGenerationExecutionCharges.total_zero,BinaryWrapperEmission.one_length,BinaryWrapperEmission.one_work,BinaryWrapperEmission.two_length,BinaryWrapperEmission.two_work,BinarySeedWrapperEmission.three_length,BinarySeedWrapperEmission.three_work]
    omega
  · split
    · simp only [BinaryGenerationExecutionCharges.total_addWrapper,BinaryGenerationExecutionCharges.total_zero,BinaryWrapperEmission.one_length,BinaryWrapperEmission.one_work,BinaryWrapperEmission.two_length,BinaryWrapperEmission.two_work,BinarySeedWrapperEmission.three_length,BinarySeedWrapperEmission.three_work]
      omega
    · simp only [BinaryGenerationExecutionCharges.total_addWrapper,BinaryGenerationExecutionCharges.total_zero,BinaryWrapperEmission.one_length,BinaryWrapperEmission.one_work,BinaryWrapperEmission.two_length,BinaryWrapperEmission.two_work,BinarySeedWrapperEmission.three_length,BinarySeedWrapperEmission.three_work]
      omega

theorem parser_parsedGenerated_length {E : Type*} [Zero E] [Add E] (backend : BinaryRawParserContinuation.Backend E) {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) :
    let produced := (BinaryRawParserContinuation.parsedGeneratedWithFactoryExtras backend next rich frame state).1.1.1.1.1
    produced.1.1.1.2.length ≤ BinaryGenerationExecutionCharges.total produced.1.2 := by
  simp only [BinaryRawParserContinuation.parsedGeneratedWithFactoryExtras]
  split
  · simp only [BinaryGenerationExecutionCharges.total_addWrapper,BinaryGenerationExecutionCharges.total_zero,BinaryWrapperEmission.one_length,BinaryWrapperEmission.one_work,BinaryWrapperEmission.two_length,BinaryWrapperEmission.two_work,BinarySeedWrapperEmission.three_length,BinarySeedWrapperEmission.three_work]
    omega
  · split
    · simp only [BinaryGenerationExecutionCharges.total_addWrapper,BinaryGenerationExecutionCharges.total_zero,BinaryWrapperEmission.one_length,BinaryWrapperEmission.one_work,BinaryWrapperEmission.two_length,BinaryWrapperEmission.two_work,BinarySeedWrapperEmission.three_length,BinarySeedWrapperEmission.three_work]
      omega
    · simp only [BinaryGenerationExecutionCharges.total_addWrapper,BinaryGenerationExecutionCharges.total_zero,BinaryWrapperEmission.one_length,BinaryWrapperEmission.one_work,BinaryWrapperEmission.two_length,BinaryWrapperEmission.two_work,BinarySeedWrapperEmission.three_length,BinarySeedWrapperEmission.three_work]
      omega

theorem parser_pair_length {E : Type*} [Zero E] [Add E] (backend : BinaryRawParserContinuation.Backend E) {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    let produced := (BinaryRawParserContinuation.pairWithFactoryExtras backend next frame state).1.1.1.1.1
    produced.1.1.1.2.length ≤ BinaryGenerationExecutionCharges.total produced.1.2 := by
  simp only [BinaryRawParserContinuation.pairWithFactoryExtras]
  simp only [BinaryGenerationExecutionCharges.total_addWrapper,BinaryGenerationExecutionCharges.total_add,BinaryWrapperEmission.two_length,BinaryWrapperEmission.two_work]
  omega

theorem parser_parsedPair_length {E : Type*} [Zero E] [Add E] (backend : BinaryRawParserContinuation.Backend E) {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    let produced := (BinaryRawParserContinuation.parsedPairWithFactoryExtras backend next frame state).1.1.1.1.1
    produced.1.1.1.2.length ≤ BinaryGenerationExecutionCharges.total produced.1.2 := by
  simp only [BinaryRawParserContinuation.parsedPairWithFactoryExtras]
  simp only [BinaryGenerationExecutionCharges.total_addWrapper,BinaryGenerationExecutionCharges.total_add,BinaryWrapperEmission.two_length,BinaryWrapperEmission.two_work]
  omega

theorem raw_length (rich : Bool) (frame bits : List Bool) :
    let produced := (BinaryPromiseOpcodeRequest.rawWithFactoryExtras rich frame bits).1.1.1.1.1
    produced.1.1.1.2.length ≤ BinarySamplerExecutionCharges.total produced.1.2 := by
  simpa only [BinaryPromiseOpcodeRequest.rawWithFactoryExtras] using parser_raw_length BinaryPromiseOpcodeRequest.backend rich frame bits

theorem parsedRaw_length (rich : Bool) (frame bits : List Bool) :
    let produced := (BinaryPromiseOpcodeRequest.parsedRawWithFactoryExtras rich frame bits).1.1.1.1.1
    produced.1.1.1.2.length ≤ BinarySamplerExecutionCharges.total produced.1.2 := by
  simpa only [BinaryPromiseOpcodeRequest.parsedRawWithFactoryExtras] using parser_parsedRaw_length BinaryPromiseOpcodeRequest.backend rich frame bits

theorem generated_length {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) :
    let produced := (BinaryPromiseOpcodeRequest.generatedWithFactoryExtras next rich frame state).1.1.1.1.1
    produced.1.1.1.2.length ≤ BinaryGenerationExecutionCharges.total produced.1.2 := by
  simpa only [BinaryPromiseOpcodeRequest.generatedWithFactoryExtras] using parser_generated_length BinaryPromiseOpcodeRequest.backend next rich frame state

theorem parsedGenerated_length {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) :
    let produced := (BinaryPromiseOpcodeRequest.parsedGeneratedWithFactoryExtras next rich frame state).1.1.1.1.1
    produced.1.1.1.2.length ≤ BinaryGenerationExecutionCharges.total produced.1.2 := by
  simpa only [BinaryPromiseOpcodeRequest.parsedGeneratedWithFactoryExtras] using parser_parsedGenerated_length BinaryPromiseOpcodeRequest.backend next rich frame state

theorem pair_length {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    let produced := (BinaryPromiseOpcodeRequest.pairWithFactoryExtras next frame state).1.1.1.1.1
    produced.1.1.1.2.length ≤ BinaryGenerationExecutionCharges.total produced.1.2 := by
  simpa only [BinaryPromiseOpcodeRequest.pairWithFactoryExtras] using parser_pair_length BinaryPromiseOpcodeRequest.backend next frame state

theorem parsedPair_length {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    let produced := (BinaryPromiseOpcodeRequest.parsedPairWithFactoryExtras next frame state).1.1.1.1.1
    produced.1.1.1.2.length ≤ BinaryGenerationExecutionCharges.total produced.1.2 := by
  simpa only [BinaryPromiseOpcodeRequest.parsedPairWithFactoryExtras] using parser_parsedPair_length BinaryPromiseOpcodeRequest.backend next frame state

end Blotto.BinaryCompleteTraceHeaders
