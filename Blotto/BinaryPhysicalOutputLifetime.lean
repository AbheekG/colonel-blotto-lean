import Blotto.BinaryPhysicalRowOutput

/-! Physical array preparation, carry-index production, original-budget
arithmetic, direct tape framing and header append execute once in sequence.
The incoming decoded row list is borrowed; no native output array is built. -/
namespace Blotto.BinaryPhysicalOutputLifetime
open BinaryRationalNormalization BinarySeedPreparationSpace BinaryPRGHeapTraceUsage BinaryWordObjectArray
set_option maxHeartbeats 3000000

theorem prepared_realizes (words : List SignedWord) :
    (BinaryWordObjectArrayLifetime.prepareWithTrace words).1.Realizes words := by
  rw [BinaryWordObjectArrayLifetime.prepareWithTrace_state]
  exact prepare_realizes words

def outputWithTrace (budget : SignedWord) (header : List Bool) (words : List SignedWord) : List Bool × Trace :=
  let prepared := BinaryWordObjectArrayLifetime.prepareWithTrace words
  let indices := BooleanArrayIndexEnumeration.enumerateWithTrace words
  let emitted := BinaryPhysicalRowOutput.emitWithTrace prepared.1 budget indices.1
  have hSome : emitted.1.isSome := by
    rw [BinaryPhysicalRowOutput.emit_enumerate prepared.1 words (prepared_realizes words) budget]
    rfl
  let joined := BinaryPRGHeapPrimitiveLifetime.appendWithTrace header (emitted.1.get hSome)
  (joined.1,wrap 64 2 [prepared.2,indices.2,emitted.2,joined.2])

theorem output_state (budget : SignedWord) (header : List Bool) (words : List SignedWord) :
    (outputWithTrace budget header words).1 =
      header++BinaryStoredRowFrame.words (BinaryPhysicalRowOutput.scaledWords budget words) := by
  unfold outputWithTrace
  dsimp only
  rw [BinaryPRGHeapPrimitiveLifetime.appendWithTrace_erasure,BinaryPRGWordStoreHeapMachine.appendWithWork_erasure]
  congr 1
  exact Option.get_of_eq_some _ (BinaryPhysicalRowOutput.emit_enumerate _ words (prepared_realizes words) budget)

theorem wordWidth_le (N : ℕ) : binaryWordWidth N ≤ N+1 := by
  unfold binaryWordWidth
  exact Nat.add_le_add_right (Nat.log2_le_self N) 1

def heapCap (n W : ℕ) : ℕ := 4*n*(W+1)
def slotsCap (n W : ℕ) : ℕ := n*(2*(heapCap n W+1)+1)
def preparationBound (n W : ℕ) : ℕ :=
  n*(33*(100*(heapCap n W+1)^2)+64)+1024*(n*(heapCap n W+1)+n+1)+128

def readEnvelope (n W : ℕ) : ℕ :=
  64*BinaryReferenceVector.readBound (slotsCap n W) (n+1)+
    32*(BinaryPRGWordStoreHeapMachine.readBound (heapCap n W) (heapCap n W+1)+
      heapCap n W*(heapCap n W+1)+2*heapCap n W+5)+128

def stepEnvelope (n W : ℕ) : ℕ :=
  readEnvelope n W+BinaryQuadraticLifetime.opcodeBound W+BinaryQuadraticLifetime.opcodeFrames W+
    1024*(3*W+2)+128*(12*W+8)+256

def bound (n W header : ℕ) : ℕ :=
  preparationBound n W+n*stepEnvelope n W+32*n+128*(header+1)+256

theorem store_caps (words : List SignedWord) (W : ℕ) (hWords : ∀ word ∈ words,width word ≤ W) :
    (BinaryWordObjectArrayLifetime.prepareWithTrace words).1.heap.tape.length ≤ heapCap words.length W ∧
      (BinaryWordObjectArrayLifetime.prepareWithTrace words).1.slots.length ≤ slotsCap words.length W := by
  have hPayload := payloadBits_bound words W hWords
  have hHeap : (BinaryWordObjectArrayLifetime.prepareWithTrace words).1.heap.tape.length = payloadBits words := by
    rw [BinaryWordObjectArrayLifetime.prepareWithTrace_state,prepare_heap_length]
  have hSlots := (BinaryWordObjectArrayLifetime.prepareWithTrace words).1.slots_bound
  have hWidth := wordWidth_le (BinaryWordObjectArrayLifetime.prepareWithTrace words).1.heap.tape.length
  refine ⟨by simpa only [heapCap,hHeap] using hPayload,?_⟩
  unfold slotsCap heapCap at *
  nlinarith

theorem preparation_bound (words : List SignedWord) (W : ℕ) (hWords : ∀ word ∈ words,width word ≤ W) :
    usage (BinaryWordObjectArrayLifetime.prepareWithTrace words).2 ≤ preparationBound words.length W := by
  apply (BinaryWordObjectArrayLifetime.prepare_usage words).trans
  have hPayload : payloadBits words ≤ heapCap words.length W := payloadBits_bound words W hWords
  have hWidth := (wordWidth_le (payloadBits words)).trans (Nat.add_le_add_right hPayload 1)
  unfold BinaryWordObjectArrayLifetime.envelope BinaryPRGWordStoreHeapMachine.allocationBound preparationBound
  gcongr

theorem read_bound (words : List SignedWord) (W : ℕ) (hWords : ∀ word ∈ words,width word ≤ W) :
    BinaryWordObjectArrayAccess.envelope (BinaryWordObjectArrayLifetime.prepareWithTrace words).1
      (binaryWordWidth words.length) ≤ readEnvelope words.length W := by
  have hCaps := store_caps words W hWords
  have hWidth := wordWidth_le (BinaryWordObjectArrayLifetime.prepareWithTrace words).1.heap.tape.length
  have hI := wordWidth_le words.length
  unfold BinaryWordObjectArrayAccess.envelope BinaryWordObjectArrayAccess.heapReadEnvelope readEnvelope
    BinaryReferenceVector.readBound BinaryPRGWordStoreHeapMachine.readBound BinaryPRGWordStoreHeapMachine.skipBound
  gcongr <;> omega

theorem output_usage (budget : SignedWord) (header : List Bool) (words : List SignedWord)
    (hBV : BinaryRationalOpcode.Valid budget) (W : ℕ) (hB : width budget ≤ W)
    (hWords : ∀ word ∈ words,BinaryRationalOpcode.Valid word ∧ width word ≤ W) :
    usage (outputWithTrace budget header words).2 ≤ bound words.length W header.length := by
  have hp := preparation_bound words W (fun w hw => (hWords w hw).2)
  have hi := BooleanArrayIndexEnumeration.enumerate_usage words
  have he := BinaryPhysicalRowOutput.emit_usage (BinaryWordObjectArrayLifetime.prepareWithTrace words).1 words
    (prepared_realizes words) budget hBV (binaryWordWidth words.length) W hB hWords
    (BooleanArrayIndexEnumeration.enumerateWithTrace words).1 (BooleanArrayIndexEnumeration.enumerate_width words)
  have hStep : BinaryPhysicalRowOutput.stepEnvelope (BinaryWordObjectArrayLifetime.prepareWithTrace words).1
      (binaryWordWidth words.length) W ≤ stepEnvelope words.length W := by
    have hRead := read_bound words W (fun w hw => (hWords w hw).2)
    unfold BinaryPhysicalRowOutput.stepEnvelope stepEnvelope
    omega
  have hLength : (BooleanArrayIndexEnumeration.enumerateWithTrace words).1.length = words.length := by
    have h := congrArg List.length (BooleanArrayIndexEnumeration.enumerate_values words)
    simpa only [List.length_map,List.length_range] using h
  rw [hLength] at he
  have hEmit := he.trans (Nat.add_le_add_right (Nat.mul_le_mul_left words.length hStep) 32)
  unfold outputWithTrace
  dsimp only
  have hw := wrap_usage 64 2 [(BinaryWordObjectArrayLifetime.prepareWithTrace words).2,
    (BooleanArrayIndexEnumeration.enumerateWithTrace words).2,
    (BinaryPhysicalRowOutput.emitWithTrace (BinaryWordObjectArrayLifetime.prepareWithTrace words).1 budget
      (BooleanArrayIndexEnumeration.enumerateWithTrace words).1).2,
    (BinaryPRGHeapPrimitiveLifetime.appendWithTrace header
      ((BinaryPhysicalRowOutput.emitWithTrace (BinaryWordObjectArrayLifetime.prepareWithTrace words).1 budget
        (BooleanArrayIndexEnumeration.enumerateWithTrace words).1).1.get (by
          rw [BinaryPhysicalRowOutput.emit_enumerate _ words (prepared_realizes words) budget]; rfl))).2]
  have ha := BinaryReferenceVectorLifetime.append_usage header
    ((BinaryPhysicalRowOutput.emitWithTrace (BinaryWordObjectArrayLifetime.prepareWithTrace words).1 budget
      (BooleanArrayIndexEnumeration.enumerateWithTrace words).1).1.get (by
        rw [BinaryPhysicalRowOutput.emit_enumerate _ words (prepared_realizes words) budget]; rfl))
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  unfold bound
  omega

theorem all_prefix (budget : SignedWord) (header : List Bool) (words : List SignedWord)
    (hBV : BinaryRationalOpcode.Valid budget) (W : ℕ) (hB : width budget ≤ W)
    (hWords : ∀ word ∈ words,BinaryRationalOpcode.Valid word ∧ width word ≤ W) (borrowed steps : ℕ) :
    retainedHeap borrowed (outputWithTrace budget header words).2 steps ≤ borrowed+bound words.length W header.length ∧
      framePeak ((outputWithTrace budget header words).2.take steps) ≤ bound words.length W header.length :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (output_usage budget header words hBV W hB hWords) borrowed steps

end Blotto.BinaryPhysicalOutputLifetime
