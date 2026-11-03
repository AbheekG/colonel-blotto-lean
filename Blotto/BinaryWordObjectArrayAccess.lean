import Blotto.BinaryWordObjectArrayLifetime

/-! Actual slot parsing feeds the selected stored pointer to the existing
physical object reader. Every returned word is the original row entry. Reached
heap/vector lengths derive work and retained-prefix bounds; invalid indices
stop at slot EOF. Semantic row witnesses are never executed or copied. -/
namespace Blotto.BinaryWordObjectArrayAccess
open BinaryRationalNormalization BinaryPRGWordStoreHeap BinaryWordObjectArray
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
set_option maxHeartbeats 2000000

def getWithTrace {n : ℕ} (store : Store n) (index : List Bool) : Option SignedWord × Trace :=
  let slot := BinaryReferenceVectorLifetime.readWithTrace store.slots index
  match slot.1 with
  | none => (none,wrap 16 2 [slot.2])
  | some pointer =>
      let object := BinaryPRGHeapAllocationLifetime.readWithTrace store.heap.tape pointer
      (match object.1 with | some (.leaf word) => some word | _ => none,wrap 48 2 [slot.2,object.2])

theorem get_state {n : ℕ} (store : Store n) (index : List Bool) : (getWithTrace store index).1 = (getWithWork store index).1 := by
  unfold getWithTrace getWithWork
  dsimp only
  rw [BinaryReferenceVectorLifetime.read_state]
  cases hSlot : (BinaryReferenceVector.readWithWork store.slots index).1 with
  | none => simp only
  | some pointer =>
      simp only [BinaryPRGHeapAllocationLifetime.readWithTrace_erasure]
      rfl

theorem get_realizes {n : ℕ} (store : Store n) (words : List SignedWord) (h : store.Realizes words) (index : List Bool) :
    (getWithTrace store index).1 = words[BinaryBigEndian.littleValue index]? := by
  rw [get_state,getWithWork_state]
  exact BinaryWordObjectArray.get_state store words h index

theorem get_width_le_tape {n : ℕ} (store : Store n)
    (index : List Bool) (word : SignedWord)
    (hRead : (getWithTrace store index).1 = some word) :
    width word ≤ store.heap.tape.length := by
  rw [get_state,getWithWork_state] at hRead
  exact BinaryWordObjectArray.get_width_le_tape store index word hRead

def heapReadEnvelope (cells : ℕ) : ℕ :=
  32*(BinaryPRGWordStoreHeapMachine.readBound cells (binaryWordWidth cells)+
    cells*binaryWordWidth cells+2*cells+5)

def envelope {n : ℕ} (store : Store n) (indexWidth : ℕ) : ℕ :=
  64*BinaryReferenceVector.readBound store.slots.length indexWidth+heapReadEnvelope store.heap.tape.length+128

theorem get_usage {n : ℕ} (store : Store n) (index : List Bool) :
    usage (getWithTrace store index).2 ≤ envelope store index.length := by
  have hSlotWork := BinaryReferenceVector.readWithWork_bound store.slots index
  have hSlot := (BinaryReferenceVectorLifetime.read_usage store.slots index).trans (Nat.mul_le_mul_left 64 hSlotWork)
  unfold getWithTrace
  dsimp only
  cases hRead : (BinaryReferenceVectorLifetime.readWithTrace store.slots index).1 with
  | none =>
      simp only
      have hw := wrap_usage 16 2 [(BinaryReferenceVectorLifetime.readWithTrace store.slots index).2]
      simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
      unfold envelope
      omega

  | some pointer =>
      simp only
      obtain ⟨pointers,words,hLength,hSlots,hLinks⟩ := store.realized
      have hIndex : pointers[BinaryBigEndian.littleValue index]? = some pointer := by
        rwa [BinaryReferenceVectorLifetime.read_state,hSlots,BinaryReferenceVector.read_encoded] at hRead
      obtain ⟨word,hWord⟩ := hLinks.contains pointer (BinaryWordObjectArray.getElemOption_mem _ _ _ hIndex)
      have hData := BinaryPRGHeapAllocationLifetime.readWithTrace_bound store.heap.tape pointer
      have hCost := BinaryPRGWordStoreHeapMachine.readContains_bounds hWord
      have hObject : usage (BinaryPRGHeapAllocationLifetime.readWithTrace store.heap.tape pointer).2 ≤
          heapReadEnvelope store.heap.tape.length := by
        unfold usage BinaryPRGHeapPrimitiveLifetime.price heapReadEnvelope at *
        omega
      have hw := wrap_usage 48 2 [(BinaryReferenceVectorLifetime.readWithTrace store.slots index).2,
        (BinaryPRGHeapAllocationLifetime.readWithTrace store.heap.tape pointer).2]
      simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
      unfold envelope
      omega

theorem native_lookup_work_le_envelope {n : ℕ}
    (store : Store n) (index : List Bool) :
    (getWithWork store index).2 ≤ envelope store index.length := by
  have h := getWithWork_bound store index
  unfold BinaryWordObjectArray.readBound envelope heapReadEnvelope at *
  omega

theorem all_prefix {n : ℕ} (store : Store n) (index : List Bool) (borrowed steps : ℕ) :
    retainedHeap borrowed (getWithTrace store index).2 steps ≤ borrowed+envelope store index.length ∧
      framePeak ((getWithTrace store index).2.take steps) ≤ envelope store index.length :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (get_usage store index) borrowed steps

end Blotto.BinaryWordObjectArrayAccess
