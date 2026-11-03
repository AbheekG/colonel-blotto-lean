import Blotto.BinaryWordObjectArrayAccess
import Blotto.BinarySeedArrayAccess

/-! Concrete physical word-array preparation and lookup refine actual PRG
value/length/poor-resource tables. Original raw length supplies closed tape,
work and retained-prefix bounds. The Boolean index stream supplies valid
index words. This is an executable primitive/interface refinement; replacing
every full sampler caller and pricing the initial native projection remain
separate obligations. No payload or access-price oracle is introduced. -/
namespace Blotto.PRGPhysicalArrayInterface
open BinaryRationalNormalization BinaryWordObjectArray BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
set_option maxHeartbeats 3000000

def prepareTable {n : ℕ} (table : FixedArrayTable n SignedWord) :=
  BinaryWordObjectArrayLifetime.prepareWithTrace table.data.toList

theorem table_read {n : ℕ} (table : FixedArrayTable n SignedWord) (index : List Bool) (j : Fin n)
    (hIndex : BinaryBigEndian.littleValue index = j.val) :
    (BinaryWordObjectArrayAccess.getWithTrace (prepareTable table).1 index).1 = some (table.read j) := by
  simp only [prepareTable,BinaryWordObjectArrayLifetime.prepareWithTrace_state]
  rw [BinaryWordObjectArrayAccess.get_realizes _ _ (prepare_realizes table.data.toList),hIndex]
  simp only [List.getElem?_eq_getElem (by rw [Array.length_toList,table.size]; exact j.isLt),Array.getElem_toList,FixedArrayTable.read]

def tables {n : ℕ} (request : BinaryPRGRequest.Request n) : List (FixedArrayTable n SignedWord) :=
  [request.prepared.original.values,request.prepared.lengths,request.prepared.poorResources]

theorem table_word_width (frame : List Bool) (parsed : PRGNativeArrayControl.Parsed)
    (hRead : (BinaryPRGRawRequestLifetime.readWithTrace frame).1 = some parsed) :
    ∀ table ∈ tables parsed.1.2.request,∀ j,width (table.read j) ≤ 9*frame.length+22 := by
  have hOld := (BinaryPRGRawRequestLifetime.readWithTrace_state frame).symm.trans hRead
  have hS := BinaryPRGFrameCostJoin.read_stored_width frame parsed hOld
  have hOriginal := (BinaryPRGPreparationWork.original_widths parsed.1.2.request.prepared.original).2.2.1
  have hPrepare := parsed.1.2.request.valid.1
  intro table hTable j
  simp only [tables,List.mem_cons,List.not_mem_nil,or_false] at hTable
  rcases hTable with rfl|rfl|rfl
  · have hw := hOriginal j
    omega
  · have hw := BinaryPRGPreparationWork.lengths_width parsed.1.2.request.prepared.original j
    rw [← hPrepare] at hw
    omega
  · have hw := BinaryPRGPreparationWork.poorResources_width parsed.1.2.request.prepared.original j
    rw [← hPrepare] at hw
    omega

theorem table_list_width {n W : ℕ} (table : FixedArrayTable n SignedWord) (h : ∀ j,width (table.read j) ≤ W) :
    ∀ word ∈ table.data.toList,width word ≤ W := by
  intro word hWord
  obtain ⟨i,hi,hValue⟩ := List.mem_iff_getElem.mp hWord
  let j : Fin n := ⟨i,by simpa only [Array.length_toList,table.size] using hi⟩
  have hj : table.read j = word := by
    simpa only [Array.getElem_toList,FixedArrayTable.read] using hValue
  rw [← hj]
  exact h j

def heapCap (length : ℕ) : ℕ := 4*length*(9*length+23)
def slotsCap (length : ℕ) : ℕ := length*(2*(heapCap length+1)+1)

theorem raw_payload_bound (frame : List Bool) (parsed : PRGNativeArrayControl.Parsed)
    (hRead : (BinaryPRGRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (table : FixedArrayTable parsed.1.1 SignedWord) (hTable : table ∈ tables parsed.1.2.request) :
    payloadBits table.data.toList ≤ heapCap frame.length := by
  have hw := payloadBits_bound table.data.toList (9*frame.length+22)
    (table_list_width table (table_word_width frame parsed hRead table hTable))
  rw [Array.length_toList,table.size] at hw
  have hn := PRGNativeArrayControl.dimension_bound frame parsed hRead
  unfold heapCap
  nlinarith

theorem wordWidth_le (N : ℕ) : binaryWordWidth N ≤ N+1 := by
  unfold binaryWordWidth
  exact Nat.add_le_add_right (Nat.log2_le_self N) 1

theorem raw_store_caps (frame : List Bool) (parsed : PRGNativeArrayControl.Parsed)
    (hRead : (BinaryPRGRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (table : FixedArrayTable parsed.1.1 SignedWord) (hTable : table ∈ tables parsed.1.2.request) :
    (prepareTable table).1.heap.tape.length ≤ heapCap frame.length ∧
      (prepareTable table).1.slots.length ≤ slotsCap frame.length := by
  have hPayload := raw_payload_bound frame parsed hRead table hTable
  have hHeap : (prepareTable table).1.heap.tape.length = payloadBits table.data.toList := by
    simp only [prepareTable,BinaryWordObjectArrayLifetime.prepareWithTrace_state,prepare_heap_length]
  have hSlots := (prepareTable table).1.slots_bound
  have hSize : table.data.toList.length = parsed.1.1 := by simpa only [Array.length_toList] using table.size
  have hMul := congrArg (fun N => N*(2*binaryWordWidth (prepareTable table).1.heap.tape.length+1)) hSize
  have hSlots' := hSlots.trans hMul.le
  have hWidth := wordWidth_le (prepareTable table).1.heap.tape.length
  have hn := PRGNativeArrayControl.dimension_bound frame parsed hRead
  refine ⟨by omega,?_⟩
  unfold slotsCap
  nlinarith

def preparationBound (length : ℕ) : ℕ :=
  length*(33*(100*(heapCap length+1)^2)+64)+1024*(length*(heapCap length+1)+length+1)+128

theorem raw_envelope_bound (frame : List Bool) (parsed : PRGNativeArrayControl.Parsed)
    (hRead : (BinaryPRGRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (table : FixedArrayTable parsed.1.1 SignedWord) (hTable : table ∈ tables parsed.1.2.request) :
    BinaryWordObjectArrayLifetime.envelope table.data.toList ≤ preparationBound frame.length := by
  have hPayload := raw_payload_bound frame parsed hRead table hTable
  have hWidth := (wordWidth_le (payloadBits table.data.toList)).trans (Nat.add_le_add_right hPayload 1)
  have hn : table.data.toList.length ≤ frame.length := by
    simpa only [Array.length_toList,table.size] using PRGNativeArrayControl.dimension_bound frame parsed hRead
  unfold BinaryWordObjectArrayLifetime.envelope BinaryPRGWordStoreHeapMachine.allocationBound preparationBound
  gcongr

theorem raw_preparation_bound (frame : List Bool) (parsed : PRGNativeArrayControl.Parsed)
    (hRead : (BinaryPRGRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (table : FixedArrayTable parsed.1.1 SignedWord) (hTable : table ∈ tables parsed.1.2.request) :
    usage (prepareTable table).2 ≤ preparationBound frame.length :=
  (BinaryWordObjectArrayLifetime.prepare_usage table.data.toList).trans (raw_envelope_bound frame parsed hRead table hTable)

theorem workEnvelope_le_source (words : List SignedWord) :
    BinaryWordObjectArrayLifetime.workEnvelope words ≤ BinaryWordObjectArrayLifetime.envelope words := by
  have hA := Nat.zero_le (words.length*BinaryPRGWordStoreHeapMachine.allocationBound (payloadBits words))
  have hP := Nat.zero_le (words.length*binaryWordWidth (payloadBits words)+words.length+1)
  unfold BinaryWordObjectArrayLifetime.workEnvelope BinaryWordObjectArrayLifetime.envelope
  nlinarith

theorem raw_preparation_work_bound (frame : List Bool) (parsed : PRGNativeArrayControl.Parsed)
    (hRead : (BinaryPRGRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (table : FixedArrayTable parsed.1.1 SignedWord) (hTable : table ∈ tables parsed.1.2.request) :
    (BinaryWordObjectArrayLifetime.prepareWithWork table.data.toList).2 ≤ preparationBound frame.length :=
  (BinaryWordObjectArrayLifetime.prepareWithWork_bound table.data.toList).trans
    ((workEnvelope_le_source table.data.toList).trans (raw_envelope_bound frame parsed hRead table hTable))

def readWorkBound (length : ℕ) : ℕ :=
  BinaryReferenceVector.readBound (slotsCap length) (length+1)+
    BinaryPRGWordStoreHeapMachine.readBound (heapCap length) (heapCap length+1)+8

def readEnvelope (length : ℕ) : ℕ :=
  64*BinaryReferenceVector.readBound (slotsCap length) (length+1)+
    32*(BinaryPRGWordStoreHeapMachine.readBound (heapCap length) (heapCap length+1)+
      heapCap length*(heapCap length+1)+2*heapCap length+5)+128

theorem raw_read_bounds (frame : List Bool) (parsed : PRGNativeArrayControl.Parsed)
    (hRead : (BinaryPRGRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (table : FixedArrayTable parsed.1.1 SignedWord) (hTable : table ∈ tables parsed.1.2.request)
    (index : List Bool) (hIndex : index ∈ (BooleanArrayIndexEnumeration.enumerateWithTrace table.data.toList).1) :
    (getWithWork (prepareTable table).1 index).2 ≤ readWorkBound frame.length ∧
      usage (BinaryWordObjectArrayAccess.getWithTrace (prepareTable table).1 index).2 ≤ readEnvelope frame.length := by
  have hCaps := raw_store_caps frame parsed hRead table hTable
  have hWidth := (wordWidth_le (prepareTable table).1.heap.tape.length).trans (Nat.add_le_add_right hCaps.1 1)
  have hI := BooleanArrayIndexEnumeration.enumerate_width table.data.toList index hIndex
  have hSize : table.data.toList.length = parsed.1.1 := by simpa only [Array.length_toList] using table.size
  rw [hSize] at hI
  have hn := PRGNativeArrayControl.dimension_bound frame parsed hRead
  have hIndexWidth : index.length ≤ frame.length+1 := hI.trans ((wordWidth_le parsed.1.1).trans (Nat.add_le_add_right hn 1))
  constructor
  · apply (getWithWork_bound _ _).trans
    unfold BinaryWordObjectArray.readBound readWorkBound BinaryReferenceVector.readBound
      BinaryPRGWordStoreHeapMachine.readBound BinaryPRGWordStoreHeapMachine.skipBound
    gcongr <;> omega
  · apply (BinaryWordObjectArrayAccess.get_usage _ _).trans
    unfold BinaryWordObjectArrayAccess.envelope BinaryWordObjectArrayAccess.heapReadEnvelope readEnvelope
      BinaryReferenceVector.readBound BinaryPRGWordStoreHeapMachine.readBound BinaryPRGWordStoreHeapMachine.skipBound
    gcongr <;> omega

theorem word_for_index {n : ℕ} (table : FixedArrayTable n SignedWord) (j : Fin n) :
    ∃ index ∈ (BooleanArrayIndexEnumeration.enumerateWithTrace table.data.toList).1,
      BinaryBigEndian.littleValue index = j.val := by
  have hValues := BooleanArrayIndexEnumeration.enumerate_values table.data.toList
  rw [Array.length_toList,table.size] at hValues
  have hMem : j.val ∈ (BooleanArrayIndexEnumeration.enumerateWithTrace table.data.toList).1.map BinaryCarryCounter.value := by
    rw [hValues]
    exact List.mem_range.mpr j.isLt
  obtain ⟨index,hIndex,hValue⟩ := List.mem_map.mp hMem
  exact ⟨index,hIndex,hValue⟩

theorem raw_native_lookup (frame : List Bool) (parsed : PRGNativeArrayControl.Parsed)
    (hRead : (BinaryPRGRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (table : FixedArrayTable parsed.1.1 SignedWord) (hTable : table ∈ tables parsed.1.2.request) (j : Fin parsed.1.1) :
    ∃ index ∈ (BooleanArrayIndexEnumeration.enumerateWithTrace table.data.toList).1,
      (BinaryWordObjectArrayAccess.getWithTrace (prepareTable table).1 index).1 = some (table.read j) ∧
      (getWithWork (prepareTable table).1 index).2 ≤ readWorkBound frame.length ∧
      usage (BinaryWordObjectArrayAccess.getWithTrace (prepareTable table).1 index).2 ≤ readEnvelope frame.length := by
  obtain ⟨index,hIndex,hValue⟩ := word_for_index table j
  exact ⟨index,hIndex,table_read table index j hValue,raw_read_bounds frame parsed hRead table hTable index hIndex⟩

theorem raw_preparation_prefix (frame : List Bool) (parsed : PRGNativeArrayControl.Parsed)
    (hRead : (BinaryPRGRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (table : FixedArrayTable parsed.1.1 SignedWord) (hTable : table ∈ tables parsed.1.2.request) (borrowed steps : ℕ) :
    retainedHeap borrowed (prepareTable table).2 steps ≤ borrowed+preparationBound frame.length ∧
      framePeak ((prepareTable table).2.take steps) ≤ preparationBound frame.length :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (raw_preparation_bound frame parsed hRead table hTable) borrowed steps

theorem raw_read_prefix (frame : List Bool) (parsed : PRGNativeArrayControl.Parsed)
    (hRead : (BinaryPRGRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (table : FixedArrayTable parsed.1.1 SignedWord) (hTable : table ∈ tables parsed.1.2.request)
    (index : List Bool) (hIndex : index ∈ (BooleanArrayIndexEnumeration.enumerateWithTrace table.data.toList).1) (borrowed steps : ℕ) :
    retainedHeap borrowed (BinaryWordObjectArrayAccess.getWithTrace (prepareTable table).1 index).2 steps ≤ borrowed+readEnvelope frame.length ∧
      framePeak ((BinaryWordObjectArrayAccess.getWithTrace (prepareTable table).1 index).2.take steps) ≤ readEnvelope frame.length :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (raw_read_bounds frame parsed hRead table hTable index hIndex).2 borrowed steps

end Blotto.PRGPhysicalArrayInterface
