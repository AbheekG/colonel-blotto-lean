import Blotto.PRGNativeArrayControl

/-! Inline Boolean seed-array contents have a concrete tape read. The stored
Boolean index drives the existing scan/borrow tape skip; no native array read
or numeric index decoder is executed by this backend. Actual array size and
the already constructed Boolean index word derive all interface bounds. -/
namespace Blotto.BinarySeedArrayAccess
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
set_option maxHeartbeats 2000000

def getWithWork (tape index : List Bool) : Option Bool × ℕ :=
  let reached := BinaryPRGWordStoreHeapMachine.skipWithWork tape index
  (reached.1.head?,reached.2.work+4)

theorem getWithWork_state (tape index : List Bool) :
    (getWithWork tape index).1 = tape[BinaryBigEndian.littleValue index]? := by
  simp only [getWithWork,BinaryPRGWordStoreHeapMachine.skipWithWork_erasure,BinaryPRGWordStoreHeap.skip_drop]
  simp [List.head?_drop]

def getWithTrace (tape index : List Bool) : Option Bool × Trace :=
  let reached := BinaryPRGHeapPrimitiveLifetime.skipWithTrace tape index
  (reached.1.head?,wrap 16 2 [reached.2])

theorem get_state (tape index : List Bool) : (getWithTrace tape index).1 = (getWithWork tape index).1 := by
  simp only [getWithTrace,getWithWork,BinaryPRGHeapPrimitiveLifetime.skipWithTrace_erasure]

def workBound (cells indexWidth : ℕ) : ℕ := BinaryPRGWordStoreHeapMachine.skipBound cells indexWidth+4

theorem getWithWork_bound (tape index : List Bool) : (getWithWork tape index).2 ≤ workBound tape.length index.length := by
  exact Nat.add_le_add_right (BinaryPRGWordStoreHeapMachine.skipWithWork_bounds tape index).1 4

def envelope (cells indexWidth : ℕ) : ℕ :=
  32*(BinaryPRGWordStoreHeapMachine.skipBound cells indexWidth+cells*indexWidth+4)

theorem get_usage (tape index : List Bool) : usage (getWithTrace tape index).2 ≤ envelope tape.length index.length := by
  have ht := BinaryPRGHeapPrimitiveLifetime.skipWithTrace_bound tape index
  have hb := BinaryPRGWordStoreHeapMachine.skipWithWork_bounds tape index
  have hSkip : usage (BinaryPRGHeapPrimitiveLifetime.skipWithTrace tape index).2 ≤
      17*(BinaryPRGWordStoreHeapMachine.skipWithWork tape index).2.work+
        16*(BinaryPRGWordStoreHeapMachine.skipWithWork tape index).2.allocatedBits+1 := by
    unfold usage BinaryPRGHeapPrimitiveLifetime.price at *
    omega
  have hw := wrap_usage 16 2 [(BinaryPRGHeapPrimitiveLifetime.skipWithTrace tape index).2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change usage (getWithTrace tape index).2 ≤ _ at hw
  unfold envelope
  omega

theorem array_read {n : ℕ} (table : FixedArrayTable n Bool) (index : List Bool) (j : Fin n)
    (hIndex : BinaryBigEndian.littleValue index = j.val) :
    (getWithTrace table.data.toList index).1 = some (table.read j) := by
  rw [get_state,getWithWork_state,hIndex]
  simp only [List.getElem?_eq_getElem (by rw [Array.length_toList,table.size]; exact j.isLt),Array.getElem_toList,FixedArrayTable.read]

theorem raw_work_bound (frame : List Bool) (parsed : PRGNativeArrayControl.Parsed)
    (hRead : (BinaryPRGRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (tables : BinaryPRGSeedBlocks.Tables parsed.1.1 parsed.1.2.request.precision)
    (data : Array Bool) (hData : data ∈ PRGNativeArrayControl.seedArrays tables) (index : List Bool)
    (hIndex : index.length ≤ binaryWordWidth (BinaryPRGSeedRequestBound.seedCountBound frame.length)) :
    (getWithWork data.toList index).2 ≤ workBound (BinaryPRGSeedRequestBound.seedCountBound frame.length)
      (binaryWordWidth (BinaryPRGSeedRequestBound.seedCountBound frame.length)) := by
  have hSize := (PRGNativeArrayControl.seed_array_size tables data hData).trans (PRGNativeArrayControl.count_bound frame parsed hRead)
  have h := getWithWork_bound data.toList index
  rw [Array.length_toList] at h
  apply h.trans
  unfold workBound BinaryPRGWordStoreHeapMachine.skipBound
  gcongr

theorem all_prefix (tape index : List Bool) (borrowed steps : ℕ) :
    retainedHeap borrowed (getWithTrace tape index).2 steps ≤ borrowed+envelope tape.length index.length ∧
      framePeak ((getWithTrace tape index).2.take steps) ≤ envelope tape.length index.length :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (get_usage tape index) borrowed steps

theorem raw_stream_bounds (frame : List Bool) (parsed : PRGNativeArrayControl.Parsed)
    (hRead : (BinaryPRGRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (tables : BinaryPRGSeedBlocks.Tables parsed.1.1 parsed.1.2.request.precision)
    (data : Array Bool) (hData : data ∈ PRGNativeArrayControl.seedArrays tables) (index : List Bool)
    (hIndex : index ∈ (BooleanArrayIndexEnumeration.enumerateWithTrace data.toList).1) :
    (getWithWork data.toList index).2 ≤ workBound (BinaryPRGSeedRequestBound.seedCountBound frame.length)
        (binaryWordWidth (BinaryPRGSeedRequestBound.seedCountBound frame.length)) ∧
      usage (getWithTrace data.toList index).2 ≤ envelope (BinaryPRGSeedRequestBound.seedCountBound frame.length)
        (binaryWordWidth (BinaryPRGSeedRequestBound.seedCountBound frame.length)) := by
  have hWidth := (PRGNativeArrayControl.raw_seed_index_words frame parsed hRead tables data hData).2 index hIndex
  have hSize := (PRGNativeArrayControl.seed_array_size tables data hData).trans
    (PRGNativeArrayControl.count_bound frame parsed hRead)
  refine ⟨raw_work_bound frame parsed hRead tables data hData index hWidth,?_⟩
  apply (get_usage data.toList index).trans
  rw [Array.length_toList]
  unfold envelope BinaryPRGWordStoreHeapMachine.skipBound
  gcongr

theorem raw_stream_prefix (frame : List Bool) (parsed : PRGNativeArrayControl.Parsed)
    (hRead : (BinaryPRGRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (tables : BinaryPRGSeedBlocks.Tables parsed.1.1 parsed.1.2.request.precision)
    (data : Array Bool) (hData : data ∈ PRGNativeArrayControl.seedArrays tables) (index : List Bool)
    (hIndex : index ∈ (BooleanArrayIndexEnumeration.enumerateWithTrace data.toList).1) (borrowed steps : ℕ) :
    retainedHeap borrowed (getWithTrace data.toList index).2 steps ≤
        borrowed+envelope (BinaryPRGSeedRequestBound.seedCountBound frame.length)
          (binaryWordWidth (BinaryPRGSeedRequestBound.seedCountBound frame.length)) ∧
      framePeak ((getWithTrace data.toList index).2.take steps) ≤
        envelope (BinaryPRGSeedRequestBound.seedCountBound frame.length)
          (binaryWordWidth (BinaryPRGSeedRequestBound.seedCountBound frame.length)) :=
  BinaryPRGHeapTraceUsage.all_prefix _ _
    (raw_stream_bounds frame parsed hRead tables data hData index hIndex).2 borrowed steps

end Blotto.BinarySeedArrayAccess
