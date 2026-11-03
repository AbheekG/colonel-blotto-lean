import Blotto.BinaryCacheCompleteArithmeticEntryWork

/-! Complete parser/preparation/resource/cache/terminal/output entry sums for
all six selected request routes. Accepted-frame certificates are derived from
the actual parser branch. Pair costs use the first actual returned entropy state. -/
namespace Blotto.BinaryCompleteRequestArithmeticEntryWork
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryTracePlanMeasured
open BinaryTerminalPhysicalAllowanceCache (Parsed)
set_option autoImplicit false
set_option maxHeartbeats 1000000

def afterRead (decoded : Option Parsed) (accept : (parsed : Parsed) → decoded=some parsed → ℕ) : ℕ :=
  match (generalizing := false) h : decoded with
  | none => 0
  | some parsed => accept parsed h

theorem afterRead_none {decoded : Option Parsed} (accept : (parsed : Parsed) → decoded=some parsed → ℕ)
    (h : decoded=none) : afterRead decoded accept=0 := by
  cases h
  rfl

theorem afterRead_some {decoded : Option Parsed} (accept : (parsed : Parsed) → decoded=some parsed → ℕ)
    (parsed : Parsed) (h : decoded=some parsed) : afterRead decoded accept=accept parsed h := by
  cases h
  rfl

def rawCost (rich : Bool) (frame bits : List Bool) : ℕ :=
  BinaryParserArithmeticEntryWork.checkedGame frame+
    afterRead (BinaryPromiseOpcodeRequest.backend.run frame).1.1.1.1 (fun parsed hParsed =>
      if parsed.2=[] then
        have hOriginal : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1=some parsed :=
          (congrArg Prod.fst (BinaryRawParserContinuation.read_original BinaryPromiseOpcodeRequest.backend frame)).symm.trans hParsed
        BinaryCacheCompleteArithmeticEntryWork.seedCost frame parsed hOriginal rich bits else 0)

def generatedCost {S : Type*} (next : S → Bool × S) (rich : Bool) (frame : List Bool) (state : S) : ℕ :=
  BinaryParserArithmeticEntryWork.checkedGame frame+
    afterRead (BinaryPromiseOpcodeRequest.backend.run frame).1.1.1.1 (fun parsed hParsed =>
      if parsed.2=[] then
        have hOriginal : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1=some parsed :=
          (congrArg Prod.fst (BinaryRawParserContinuation.read_original BinaryPromiseOpcodeRequest.backend frame)).symm.trans hParsed
        BinaryCacheCompleteArithmeticEntryWork.seedCost frame parsed hOriginal rich
          (BinaryFreshGenerationPlan.generateWithEmission next parsed.1.2.logical state).1.1.1.1 else 0)

theorem raw_bound (rich : Bool) (frame bits : List Bool) :
    rawCost rich frame bits ≤ 2*listCells (BinaryPromiseOpcodeRequest.raw rich frame bits).1.1.1.2 := by
  have hp := BinaryParserArithmeticEntryWork.read_bound frame
  simp only [BinaryPromiseOpcodeRequest.raw_record,BinaryRawParserContinuation.raw_record,BinaryPromiseOpcodeRequest.backend]
  split
  · rename_i hNone
    simp only [rawCost,BinaryPromiseOpcodeRequest.backend]
    rw [afterRead_none _ hNone]
    simp only [BinaryWrapperEmission.one_trace,wrap,combine,listCells_append,listCells_under,listCells]
    omega
  · rename_i parsed hSome
    split
    · rename_i hTail
      have hOriginal : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1=some parsed :=
        (congrArg Prod.fst (BinaryRawParserContinuation.read_original BinaryPromiseOpcodeRequest.backend frame)).symm.trans hSome
      have hs := BinaryCacheCompleteArithmeticEntryWork.seed_bound frame parsed hOriginal rich bits
      simp only [rawCost,BinaryPromiseOpcodeRequest.backend]
      rw [afterRead_some _ parsed hSome]
      simp only [hTail,ite_true,BinaryWrapperEmission.two_trace,BinarySeedWrapperEmission.three_trace,
        wrap,combine,listCells_append,listCells_under,listCells]
      omega
    · rename_i hTail
      simp only [rawCost,BinaryPromiseOpcodeRequest.backend]
      rw [afterRead_some _ parsed hSome]
      simp only [hTail,ite_false,BinaryWrapperEmission.one_trace,wrap,combine,listCells_append,listCells_under,listCells]
      omega

theorem parsedRaw_bound (rich : Bool) (frame bits : List Bool) :
    rawCost rich frame bits ≤ 2*listCells (BinaryPromiseOpcodeRequest.parsedRaw rich frame bits).1.1.1.2 := by
  have hp := BinaryParserArithmeticEntryWork.read_bound frame
  simp only [BinaryPromiseOpcodeRequest.parsedRaw_record,BinaryRawParserContinuation.parsedRaw_record,BinaryPromiseOpcodeRequest.backend]
  split
  · rename_i hNone
    simp only [rawCost,BinaryPromiseOpcodeRequest.backend]
    rw [afterRead_none _ hNone]
    simp only [BinaryWrapperEmission.one_trace,wrap,combine,listCells_append,listCells_under,listCells]
    omega
  · rename_i parsed hSome
    split
    · rename_i hTail
      have hOriginal : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1=some parsed :=
        (congrArg Prod.fst (BinaryRawParserContinuation.read_original BinaryPromiseOpcodeRequest.backend frame)).symm.trans hSome
      have hs := BinaryCacheCompleteArithmeticEntryWork.seed_bound frame parsed hOriginal rich bits
      simp only [rawCost,BinaryPromiseOpcodeRequest.backend]
      rw [afterRead_some _ parsed hSome]
      simp only [hTail,ite_true,BinaryWrapperEmission.two_trace,BinarySeedWrapperEmission.three_trace,
        wrap,combine,listCells_append,listCells_under,listCells]
      omega
    · rename_i hTail
      simp only [rawCost,BinaryPromiseOpcodeRequest.backend]
      rw [afterRead_some _ parsed hSome]
      simp only [hTail,ite_false,BinaryWrapperEmission.one_trace,wrap,combine,listCells_append,listCells_under,listCells]
      omega

theorem generated_bound {S : Type*} (next : S → Bool × S) (rich : Bool) (frame : List Bool) (state : S) :
    generatedCost next rich frame state ≤ 2*listCells (BinaryPromiseOpcodeRequest.generated next rich frame state).1.1.1.2 := by
  have hp := BinaryParserArithmeticEntryWork.read_bound frame
  simp only [BinaryPromiseOpcodeRequest.generated_record,BinaryRawParserContinuation.generated_record,BinaryPromiseOpcodeRequest.backend]
  split
  · rename_i hNone
    simp only [generatedCost,BinaryPromiseOpcodeRequest.backend]
    rw [afterRead_none _ hNone]
    simp only [BinaryWrapperEmission.one_trace,wrap,combine,listCells_append,listCells_under,listCells]
    omega
  · rename_i parsed hSome
    split
    · rename_i hTail
      have hOriginal : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1=some parsed :=
        (congrArg Prod.fst (BinaryRawParserContinuation.read_original BinaryPromiseOpcodeRequest.backend frame)).symm.trans hSome
      have hs := BinaryCacheCompleteArithmeticEntryWork.seed_bound frame parsed hOriginal rich (BinaryFreshGenerationPlan.generateWithEmission next parsed.1.2.logical state).1.1.1.1
      simp only [generatedCost,BinaryPromiseOpcodeRequest.backend]
      rw [afterRead_some _ parsed hSome]
      simp only [hTail,ite_true,BinaryWrapperEmission.two_trace,BinarySeedWrapperEmission.three_trace,
        wrap,combine,listCells_append,listCells_under,listCells]
      omega
    · rename_i hTail
      simp only [generatedCost,BinaryPromiseOpcodeRequest.backend]
      rw [afterRead_some _ parsed hSome]
      simp only [hTail,ite_false,BinaryWrapperEmission.one_trace,wrap,combine,listCells_append,listCells_under,listCells]
      omega

theorem parsedGenerated_bound {S : Type*} (next : S → Bool × S) (rich : Bool) (frame : List Bool) (state : S) :
    generatedCost next rich frame state ≤ 2*listCells (BinaryPromiseOpcodeRequest.parsedGenerated next rich frame state).1.1.1.2 := by
  have hp := BinaryParserArithmeticEntryWork.read_bound frame
  simp only [BinaryPromiseOpcodeRequest.parsedGenerated_record,BinaryRawParserContinuation.parsedGenerated_record,BinaryPromiseOpcodeRequest.backend]
  split
  · rename_i hNone
    simp only [generatedCost,BinaryPromiseOpcodeRequest.backend]
    rw [afterRead_none _ hNone]
    simp only [BinaryWrapperEmission.one_trace,wrap,combine,listCells_append,listCells_under,listCells]
    omega
  · rename_i parsed hSome
    split
    · rename_i hTail
      have hOriginal : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1=some parsed :=
        (congrArg Prod.fst (BinaryRawParserContinuation.read_original BinaryPromiseOpcodeRequest.backend frame)).symm.trans hSome
      have hs := BinaryCacheCompleteArithmeticEntryWork.seed_bound frame parsed hOriginal rich (BinaryFreshGenerationPlan.generateWithEmission next parsed.1.2.logical state).1.1.1.1
      simp only [generatedCost,BinaryPromiseOpcodeRequest.backend]
      rw [afterRead_some _ parsed hSome]
      simp only [hTail,ite_true,BinaryWrapperEmission.two_trace,BinarySeedWrapperEmission.three_trace,
        wrap,combine,listCells_append,listCells_under,listCells]
      omega
    · rename_i hTail
      simp only [generatedCost,BinaryPromiseOpcodeRequest.backend]
      rw [afterRead_some _ parsed hSome]
      simp only [hTail,ite_false,BinaryWrapperEmission.one_trace,wrap,combine,listCells_append,listCells_under,listCells]
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

theorem raw_complete_joint : ∃ C d : ℕ,∀ (rich : Bool) (frame bits : List Bool),
    let produced := BinaryPromiseOpcodeRequest.raw rich frame bits
    rawCost rich frame bits+produced.1.1.2+BinaryBigEndian.littleValue produced.1.1.1.1.2+usage produced.1.1.1.2+
      BinarySamplerExecutionCharges.total produced.1.2+produced.2.1.1+produced.2.1.2+produced.2.2.1.1.1.1.1.1.1.1.1.1+produced.2.2.1.1.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.2+produced.2.2.1.1.1.1.2+produced.2.2.1.1.1.2+produced.2.2.1.1.2+produced.2.2.1.2+produced.2.2.2.1.1.1.1.1.1+produced.2.2.2.1.1.1.1.1.2+produced.2.2.2.1.1.1.1.2+produced.2.2.2.1.1.1.2+produced.2.2.2.1.1.2+produced.2.2.2.1.2+produced.2.2.2.2 ≤ C*(frame.length+1)^d := by
  obtain ⟨C,d,hJoint⟩ := BinaryPromiseOpcodeBounds.raw_joint
  obtain ⟨P,e,hEntry⟩ := raw_uniform
  refine ⟨P+C,max d e,?_⟩
  intro rich frame bits
  have he := hEntry rich frame bits
  have ho := hJoint rich frame bits
  dsimp only at ho
  have hX : 0 < frame.length+1 := by omega
  have hd := Nat.mul_le_mul_left C (Nat.pow_le_pow_right hX (Nat.le_max_left d e))
  have hp := Nat.mul_le_mul_left P (Nat.pow_le_pow_right hX (Nat.le_max_right d e))
  have hs := (Nat.add_le_add he ho).trans (Nat.add_le_add hp hd)
  simpa only [Nat.add_assoc,Nat.add_mul] using hs


theorem parsedRaw_complete_joint : ∃ C d : ℕ,∀ (rich : Bool) (frame bits : List Bool),
    let produced := BinaryPromiseOpcodeRequest.parsedRaw rich frame bits
    rawCost rich frame bits+produced.1.1.2+BinaryBigEndian.littleValue produced.1.1.1.1.2+usage produced.1.1.1.2+
      BinarySamplerExecutionCharges.total produced.1.2+produced.2.1.1+produced.2.1.2+produced.2.2.1.1.1.1.1.1.1.1.1.1+produced.2.2.1.1.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.2+produced.2.2.1.1.1.1.2+produced.2.2.1.1.1.2+produced.2.2.1.1.2+produced.2.2.1.2+produced.2.2.2.1.1.1.1.1.1+produced.2.2.2.1.1.1.1.1.2+produced.2.2.2.1.1.1.1.2+produced.2.2.2.1.1.1.2+produced.2.2.2.1.1.2+produced.2.2.2.1.2+produced.2.2.2.2 ≤ C*(frame.length+1)^d := by
  obtain ⟨C,d,hJoint⟩ := BinaryPromiseOpcodeBounds.parsedRaw_joint
  obtain ⟨P,e,hEntry⟩ := parsedRaw_uniform
  refine ⟨P+C,max d e,?_⟩
  intro rich frame bits
  have he := hEntry rich frame bits
  have ho := hJoint rich frame bits
  dsimp only at ho
  have hX : 0 < frame.length+1 := by omega
  have hd := Nat.mul_le_mul_left C (Nat.pow_le_pow_right hX (Nat.le_max_left d e))
  have hp := Nat.mul_le_mul_left P (Nat.pow_le_pow_right hX (Nat.le_max_right d e))
  have hs := (Nat.add_le_add he ho).trans (Nat.add_le_add hp hd)
  simpa only [Nat.add_assoc,Nat.add_mul] using hs


theorem generated_complete_joint : ∃ C d : ℕ,∀ {S : Type*} (next : S → Bool × S) (rich : Bool) (frame : List Bool) (state : S),
    let produced := BinaryPromiseOpcodeRequest.generated next rich frame state
    generatedCost next rich frame state+produced.1.1.2+BinaryBigEndian.littleValue produced.1.1.1.1.2+usage produced.1.1.1.2+
      BinaryGenerationExecutionCharges.total produced.1.2+produced.2.1.1+produced.2.1.2+produced.2.2.1.1.1.1.1.1.1.1.1.1+produced.2.2.1.1.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.2+produced.2.2.1.1.1.1.2+produced.2.2.1.1.1.2+produced.2.2.1.1.2+produced.2.2.1.2+produced.2.2.2.1.1.1.1.1.1+produced.2.2.2.1.1.1.1.1.2+produced.2.2.2.1.1.1.1.2+produced.2.2.2.1.1.1.2+produced.2.2.2.1.1.2+produced.2.2.2.1.2+produced.2.2.2.2 ≤ C*(frame.length+1)^d := by
  obtain ⟨C,d,hJoint⟩ := BinaryPromiseOpcodeBounds.generated_joint
  obtain ⟨P,e,hEntry⟩ := generated_uniform
  refine ⟨P+C,max d e,?_⟩
  intro S next rich frame state
  have he := hEntry next rich frame state
  have ho := hJoint next rich frame state
  dsimp only at ho
  have hX : 0 < frame.length+1 := by omega
  have hd := Nat.mul_le_mul_left C (Nat.pow_le_pow_right hX (Nat.le_max_left d e))
  have hp := Nat.mul_le_mul_left P (Nat.pow_le_pow_right hX (Nat.le_max_right d e))
  have hs := (Nat.add_le_add he ho).trans (Nat.add_le_add hp hd)
  simpa only [Nat.add_assoc,Nat.add_mul] using hs


theorem parsedGenerated_complete_joint : ∃ C d : ℕ,∀ {S : Type*} (next : S → Bool × S) (rich : Bool) (frame : List Bool) (state : S),
    let produced := BinaryPromiseOpcodeRequest.parsedGenerated next rich frame state
    generatedCost next rich frame state+produced.1.1.2+BinaryBigEndian.littleValue produced.1.1.1.1.2+usage produced.1.1.1.2+
      BinaryGenerationExecutionCharges.total produced.1.2+produced.2.1.1+produced.2.1.2+produced.2.2.1.1.1.1.1.1.1.1.1.1+produced.2.2.1.1.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.2+produced.2.2.1.1.1.1.2+produced.2.2.1.1.1.2+produced.2.2.1.1.2+produced.2.2.1.2+produced.2.2.2.1.1.1.1.1.1+produced.2.2.2.1.1.1.1.1.2+produced.2.2.2.1.1.1.1.2+produced.2.2.2.1.1.1.2+produced.2.2.2.1.1.2+produced.2.2.2.1.2+produced.2.2.2.2 ≤ C*(frame.length+1)^d := by
  obtain ⟨C,d,hJoint⟩ := BinaryPromiseOpcodeBounds.parsedGenerated_joint
  obtain ⟨P,e,hEntry⟩ := parsedGenerated_uniform
  refine ⟨P+C,max d e,?_⟩
  intro S next rich frame state
  have he := hEntry next rich frame state
  have ho := hJoint next rich frame state
  dsimp only at ho
  have hX : 0 < frame.length+1 := by omega
  have hd := Nat.mul_le_mul_left C (Nat.pow_le_pow_right hX (Nat.le_max_left d e))
  have hp := Nat.mul_le_mul_left P (Nat.pow_le_pow_right hX (Nat.le_max_right d e))
  have hs := (Nat.add_le_add he ho).trans (Nat.add_le_add hp hd)
  simpa only [Nat.add_assoc,Nat.add_mul] using hs


theorem pair_complete_joint : ∃ C d : ℕ,∀ {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S),
    let produced := BinaryPromiseOpcodeRequest.pair next frame state
    pairCost next frame state+produced.1.1.2+BinaryBigEndian.littleValue produced.1.1.1.1.2.1+BinaryBigEndian.littleValue produced.1.1.1.1.2.2+usage produced.1.1.1.2+
      BinaryGenerationExecutionCharges.total produced.1.2+produced.2.1.1+produced.2.1.2+produced.2.2.1.1.1.1.1.1.1.1.1.1+produced.2.2.1.1.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.2+produced.2.2.1.1.1.1.2+produced.2.2.1.1.1.2+produced.2.2.1.1.2+produced.2.2.1.2+produced.2.2.2.1.1.1.1.1.1+produced.2.2.2.1.1.1.1.1.2+produced.2.2.2.1.1.1.1.2+produced.2.2.2.1.1.1.2+produced.2.2.2.1.1.2+produced.2.2.2.1.2+produced.2.2.2.2 ≤ C*(frame.length+1)^d := by
  obtain ⟨C,d,hJoint⟩ := BinaryPromiseOpcodeBounds.pair_joint
  obtain ⟨P,e,hEntry⟩ := pair_uniform
  refine ⟨P+C,max d e,?_⟩
  intro S next frame state
  have he := hEntry next frame state
  have ho := hJoint next frame state
  dsimp only at ho
  have hX : 0 < frame.length+1 := by omega
  have hd := Nat.mul_le_mul_left C (Nat.pow_le_pow_right hX (Nat.le_max_left d e))
  have hp := Nat.mul_le_mul_left P (Nat.pow_le_pow_right hX (Nat.le_max_right d e))
  have hs := (Nat.add_le_add he ho).trans (Nat.add_le_add hp hd)
  simpa only [Nat.add_assoc,Nat.add_mul] using hs


theorem parsedPair_complete_joint : ∃ C d : ℕ,∀ {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S),
    let produced := BinaryPromiseOpcodeRequest.parsedPair next frame state
    parsedPairCost next frame state+produced.1.1.2+BinaryBigEndian.littleValue produced.1.1.1.1.2.1+BinaryBigEndian.littleValue produced.1.1.1.1.2.2+usage produced.1.1.1.2+
      BinaryGenerationExecutionCharges.total produced.1.2+produced.2.1.1+produced.2.1.2+produced.2.2.1.1.1.1.1.1.1.1.1.1+produced.2.2.1.1.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.2+produced.2.2.1.1.1.1.2+produced.2.2.1.1.1.2+produced.2.2.1.1.2+produced.2.2.1.2+produced.2.2.2.1.1.1.1.1.1+produced.2.2.2.1.1.1.1.1.2+produced.2.2.2.1.1.1.1.2+produced.2.2.2.1.1.1.2+produced.2.2.2.1.1.2+produced.2.2.2.1.2+produced.2.2.2.2 ≤ C*(frame.length+1)^d := by
  obtain ⟨C,d,hJoint⟩ := BinaryPromiseOpcodeBounds.parsedPair_joint
  obtain ⟨P,e,hEntry⟩ := parsedPair_uniform
  refine ⟨P+C,max d e,?_⟩
  intro S next frame state
  have he := hEntry next frame state
  have ho := hJoint next frame state
  dsimp only at ho
  have hX : 0 < frame.length+1 := by omega
  have hd := Nat.mul_le_mul_left C (Nat.pow_le_pow_right hX (Nat.le_max_left d e))
  have hp := Nat.mul_le_mul_left P (Nat.pow_le_pow_right hX (Nat.le_max_right d e))
  have hs := (Nat.add_le_add he ho).trans (Nat.add_le_add hp hd)
  simpa only [Nat.add_assoc,Nat.add_mul] using hs


end Blotto.BinaryCompleteRequestArithmeticEntryWork
