import Blotto.BinaryCacheReflectedExtraWork
import Blotto.BinaryCompleteRequestArithmeticEntryWork

/-! Additional actual reflected primitive/initialization work and allocated-bit
charges follow accepted parser results and actual paired entropy states through
all six selected complete request interfaces. Frame-only polynomial/width and
joint bounds preserve every preceding field and complete arithmetic entry sum. -/
namespace Blotto.BinaryCompleteRequestReflectedExtraWork
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryTerminalPhysicalAllowanceCache (Parsed)
open BinaryCompleteRequestArithmeticEntryWork (afterRead afterRead_none afterRead_some)
set_option autoImplicit false
set_option maxHeartbeats 1000000

def rawCost (rich : Bool) (frame bits : List Bool) : ℕ :=
  afterRead (BinaryPromiseOpcodeRequest.backend.run frame).1.1.1.1 (fun parsed hParsed =>
      if parsed.2=[] then
        have hOriginal : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1=some parsed :=
          (congrArg Prod.fst (BinaryRawParserContinuation.read_original BinaryPromiseOpcodeRequest.backend frame)).symm.trans hParsed
        BinaryCacheReflectedExtraWork.seedCost frame parsed hOriginal rich bits else 0)

def generatedCost {S : Type*} (next : S → Bool × S) (rich : Bool) (frame : List Bool) (state : S) : ℕ :=
  afterRead (BinaryPromiseOpcodeRequest.backend.run frame).1.1.1.1 (fun parsed hParsed =>
      if parsed.2=[] then
        have hOriginal : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1=some parsed :=
          (congrArg Prod.fst (BinaryRawParserContinuation.read_original BinaryPromiseOpcodeRequest.backend frame)).symm.trans hParsed
        BinaryCacheReflectedExtraWork.seedCost frame parsed hOriginal rich
          (BinaryFreshGenerationPlan.generateWithEmission next parsed.1.2.logical state).1.1.1.1 else 0)

def pairCost {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) : ℕ :=
  generatedCost next true frame state+
    generatedCost next false frame (BinaryPromiseOpcodeRequest.generated next true frame state).1.1.1.1.1.2

def parsedPairCost {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) : ℕ :=
  generatedCost next true frame state+
    generatedCost next false frame (BinaryPromiseOpcodeRequest.parsedGenerated next true frame state).1.1.1.1.1.2

theorem afterRead_bound (decoded : Option Parsed) (accept : (parsed : Parsed) → decoded=some parsed → ℕ)
    (B : ℕ) (h : ∀ parsed cert,accept parsed cert ≤ B) : afterRead decoded accept ≤ B := by
  cases decoded with
  | none => exact Nat.zero_le _
  | some parsed => exact h parsed rfl

theorem raw_uniform : ∃ C d : ℕ,∀ (rich : Bool) (frame bits : List Bool),
    rawCost rich frame bits ≤ C*(frame.length+1)^d := by
  obtain ⟨C,d,hSeed⟩ := BinaryCacheReflectedExtraWork.seed_uniform
  refine ⟨C,d,?_⟩
  intro rich frame bits
  unfold rawCost
  apply afterRead_bound
  intro parsed hParsed
  split
  · exact hSeed frame parsed _ rich bits
  · exact Nat.zero_le _

theorem parsedRaw_uniform : ∃ C d : ℕ,∀ (rich : Bool) (frame bits : List Bool),
    rawCost rich frame bits ≤ C*(frame.length+1)^d := raw_uniform

theorem generated_uniform : ∃ C d : ℕ,∀ {S : Type*} (next : S → Bool × S) (rich : Bool) (frame : List Bool) (state : S),
    generatedCost next rich frame state ≤ C*(frame.length+1)^d := by
  obtain ⟨C,d,hSeed⟩ := BinaryCacheReflectedExtraWork.seed_uniform
  refine ⟨C,d,?_⟩
  intro S next rich frame state
  unfold generatedCost
  apply afterRead_bound
  intro parsed hParsed
  split
  · exact hSeed frame parsed _ rich _
  · exact Nat.zero_le _

theorem parsedGenerated_uniform : ∃ C d : ℕ,∀ {S : Type*} (next : S → Bool × S) (rich : Bool) (frame : List Bool) (state : S),
    generatedCost next rich frame state ≤ C*(frame.length+1)^d := generated_uniform

theorem pair_uniform : ∃ C d : ℕ,∀ {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S),
    pairCost next frame state ≤ C*(frame.length+1)^d := by
  obtain ⟨C,d,hSingle⟩ := generated_uniform
  refine ⟨2*C,d,?_⟩
  intro S next frame state
  have hr := hSingle next true frame state
  have hp := hSingle next false frame (BinaryPromiseOpcodeRequest.generated next true frame state).1.1.1.1.1.2
  simp only [pairCost]
  nlinarith only [hr,hp]

theorem parsedPair_uniform : ∃ C d : ℕ,∀ {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S),
    parsedPairCost next frame state ≤ C*(frame.length+1)^d := by
  obtain ⟨C,d,hSingle⟩ := generated_uniform
  refine ⟨2*C,d,?_⟩
  intro S next frame state
  have hr := hSingle next true frame state
  have hp := hSingle next false frame (BinaryPromiseOpcodeRequest.parsedGenerated next true frame state).1.1.1.1.1.2
  simp only [parsedPairCost]
  nlinarith only [hr,hp]

theorem raw_width : ∃ C d : ℕ,∀ (rich : Bool) (frame bits : List Bool),
    binaryWordWidth (rawCost rich frame bits) ≤ binaryWordWidth (C*(frame.length+1)^d) := by
  obtain ⟨C,d,h⟩ := raw_uniform
  exact ⟨C,d,fun rich frame bits => binaryWordWidth_mono (h rich frame bits)⟩

theorem parsedRaw_width : ∃ C d : ℕ,∀ (rich : Bool) (frame bits : List Bool),
    binaryWordWidth (rawCost rich frame bits) ≤ binaryWordWidth (C*(frame.length+1)^d) := by
  obtain ⟨C,d,h⟩ := parsedRaw_uniform
  exact ⟨C,d,fun rich frame bits => binaryWordWidth_mono (h rich frame bits)⟩

theorem generated_width : ∃ C d : ℕ,∀ {S : Type*} (next : S → Bool × S) (rich : Bool) (frame : List Bool) (state : S),
    binaryWordWidth (generatedCost next rich frame state) ≤ binaryWordWidth (C*(frame.length+1)^d) := by
  obtain ⟨C,d,h⟩ := generated_uniform
  refine ⟨C,d,?_⟩
  intro S next rich frame state
  exact binaryWordWidth_mono (h next rich frame state)

theorem parsedGenerated_width : ∃ C d : ℕ,∀ {S : Type*} (next : S → Bool × S) (rich : Bool) (frame : List Bool) (state : S),
    binaryWordWidth (generatedCost next rich frame state) ≤ binaryWordWidth (C*(frame.length+1)^d) := by
  obtain ⟨C,d,h⟩ := parsedGenerated_uniform
  refine ⟨C,d,?_⟩
  intro S next rich frame state
  exact binaryWordWidth_mono (h next rich frame state)

theorem pair_width : ∃ C d : ℕ,∀ {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S),
    binaryWordWidth (pairCost next frame state) ≤ binaryWordWidth (C*(frame.length+1)^d) := by
  obtain ⟨C,d,h⟩ := pair_uniform
  refine ⟨C,d,?_⟩
  intro S next frame state
  exact binaryWordWidth_mono (h next frame state)

theorem parsedPair_width : ∃ C d : ℕ,∀ {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S),
    binaryWordWidth (parsedPairCost next frame state) ≤ binaryWordWidth (C*(frame.length+1)^d) := by
  obtain ⟨C,d,h⟩ := parsedPair_uniform
  refine ⟨C,d,?_⟩
  intro S next frame state
  exact binaryWordWidth_mono (h next frame state)

theorem raw_complete_joint : ∃ C d : ℕ,∀ (rich : Bool) (frame bits : List Bool),
    let produced := BinaryPromiseOpcodeRequest.raw rich frame bits
    rawCost rich frame bits+BinaryCompleteRequestArithmeticEntryWork.rawCost rich frame bits+produced.1.1.2+BinaryBigEndian.littleValue produced.1.1.1.1.2+usage produced.1.1.1.2+
      BinarySamplerExecutionCharges.total produced.1.2+produced.2.1.1+produced.2.1.2+produced.2.2.1.1.1.1.1.1.1.1.1.1+produced.2.2.1.1.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.2+produced.2.2.1.1.1.1.2+produced.2.2.1.1.1.2+produced.2.2.1.1.2+produced.2.2.1.2+produced.2.2.2.1.1.1.1.1.1+produced.2.2.2.1.1.1.1.1.2+produced.2.2.2.1.1.1.1.2+produced.2.2.2.1.1.1.2+produced.2.2.2.1.1.2+produced.2.2.2.1.2+produced.2.2.2.2 ≤ C*(frame.length+1)^d := by
  obtain ⟨C,d,hJoint⟩ := BinaryCompleteRequestArithmeticEntryWork.raw_complete_joint
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
    rawCost rich frame bits+BinaryCompleteRequestArithmeticEntryWork.rawCost rich frame bits+produced.1.1.2+BinaryBigEndian.littleValue produced.1.1.1.1.2+usage produced.1.1.1.2+
      BinarySamplerExecutionCharges.total produced.1.2+produced.2.1.1+produced.2.1.2+produced.2.2.1.1.1.1.1.1.1.1.1.1+produced.2.2.1.1.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.2+produced.2.2.1.1.1.1.2+produced.2.2.1.1.1.2+produced.2.2.1.1.2+produced.2.2.1.2+produced.2.2.2.1.1.1.1.1.1+produced.2.2.2.1.1.1.1.1.2+produced.2.2.2.1.1.1.1.2+produced.2.2.2.1.1.1.2+produced.2.2.2.1.1.2+produced.2.2.2.1.2+produced.2.2.2.2 ≤ C*(frame.length+1)^d := by
  obtain ⟨C,d,hJoint⟩ := BinaryCompleteRequestArithmeticEntryWork.parsedRaw_complete_joint
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
    generatedCost next rich frame state+BinaryCompleteRequestArithmeticEntryWork.generatedCost next rich frame state+produced.1.1.2+BinaryBigEndian.littleValue produced.1.1.1.1.2+usage produced.1.1.1.2+
      BinaryGenerationExecutionCharges.total produced.1.2+produced.2.1.1+produced.2.1.2+produced.2.2.1.1.1.1.1.1.1.1.1.1+produced.2.2.1.1.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.2+produced.2.2.1.1.1.1.2+produced.2.2.1.1.1.2+produced.2.2.1.1.2+produced.2.2.1.2+produced.2.2.2.1.1.1.1.1.1+produced.2.2.2.1.1.1.1.1.2+produced.2.2.2.1.1.1.1.2+produced.2.2.2.1.1.1.2+produced.2.2.2.1.1.2+produced.2.2.2.1.2+produced.2.2.2.2 ≤ C*(frame.length+1)^d := by
  obtain ⟨C,d,hJoint⟩ := BinaryCompleteRequestArithmeticEntryWork.generated_complete_joint
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
    generatedCost next rich frame state+BinaryCompleteRequestArithmeticEntryWork.generatedCost next rich frame state+produced.1.1.2+BinaryBigEndian.littleValue produced.1.1.1.1.2+usage produced.1.1.1.2+
      BinaryGenerationExecutionCharges.total produced.1.2+produced.2.1.1+produced.2.1.2+produced.2.2.1.1.1.1.1.1.1.1.1.1+produced.2.2.1.1.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.2+produced.2.2.1.1.1.1.2+produced.2.2.1.1.1.2+produced.2.2.1.1.2+produced.2.2.1.2+produced.2.2.2.1.1.1.1.1.1+produced.2.2.2.1.1.1.1.1.2+produced.2.2.2.1.1.1.1.2+produced.2.2.2.1.1.1.2+produced.2.2.2.1.1.2+produced.2.2.2.1.2+produced.2.2.2.2 ≤ C*(frame.length+1)^d := by
  obtain ⟨C,d,hJoint⟩ := BinaryCompleteRequestArithmeticEntryWork.parsedGenerated_complete_joint
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
    pairCost next frame state+BinaryCompleteRequestArithmeticEntryWork.pairCost next frame state+produced.1.1.2+BinaryBigEndian.littleValue produced.1.1.1.1.2.1+BinaryBigEndian.littleValue produced.1.1.1.1.2.2+usage produced.1.1.1.2+
      BinaryGenerationExecutionCharges.total produced.1.2+produced.2.1.1+produced.2.1.2+produced.2.2.1.1.1.1.1.1.1.1.1.1+produced.2.2.1.1.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.2+produced.2.2.1.1.1.1.2+produced.2.2.1.1.1.2+produced.2.2.1.1.2+produced.2.2.1.2+produced.2.2.2.1.1.1.1.1.1+produced.2.2.2.1.1.1.1.1.2+produced.2.2.2.1.1.1.1.2+produced.2.2.2.1.1.1.2+produced.2.2.2.1.1.2+produced.2.2.2.1.2+produced.2.2.2.2 ≤ C*(frame.length+1)^d := by
  obtain ⟨C,d,hJoint⟩ := BinaryCompleteRequestArithmeticEntryWork.pair_complete_joint
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
    parsedPairCost next frame state+BinaryCompleteRequestArithmeticEntryWork.parsedPairCost next frame state+produced.1.1.2+BinaryBigEndian.littleValue produced.1.1.1.1.2.1+BinaryBigEndian.littleValue produced.1.1.1.1.2.2+usage produced.1.1.1.2+
      BinaryGenerationExecutionCharges.total produced.1.2+produced.2.1.1+produced.2.1.2+produced.2.2.1.1.1.1.1.1.1.1.1.1+produced.2.2.1.1.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.2+produced.2.2.1.1.1.1.2+produced.2.2.1.1.1.2+produced.2.2.1.1.2+produced.2.2.1.2+produced.2.2.2.1.1.1.1.1.1+produced.2.2.2.1.1.1.1.1.2+produced.2.2.2.1.1.1.1.2+produced.2.2.2.1.1.1.2+produced.2.2.2.1.1.2+produced.2.2.2.1.2+produced.2.2.2.2 ≤ C*(frame.length+1)^d := by
  obtain ⟨C,d,hJoint⟩ := BinaryCompleteRequestArithmeticEntryWork.parsedPair_complete_joint
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



end Blotto.BinaryCompleteRequestReflectedExtraWork
