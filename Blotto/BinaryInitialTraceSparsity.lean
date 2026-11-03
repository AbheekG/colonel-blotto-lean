import Blotto.BinaryResourceTraceLength

/-! Structural event counts for the actual initializer traces. Positive source
allocation headers pay for the number of emitted events. No sparsity/count
observer is executed by the producer. Native representation costs are separate. -/
namespace Blotto.BinaryInitialTraceSparsity
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage BinaryRationalNormalization BinaryRationalEncoding
open BinaryPRGHeapPrimitiveLifetime (cells)
open BinaryResourceTraceLength (under_length)
set_option autoImplicit false
set_option maxHeartbeats 4000000

def Sparse (trace : Trace) : Prop := trace.length ≤ 2*cells trace+1

theorem under_sparse (depth : ℕ) (trace : Trace) (h : Sparse trace) : Sparse (under depth trace) := by
  simpa only [Sparse,under_length,BinaryPRGHeapPrimitiveLifetime.cells_under] using h

theorem combine_bound (children : List Trace) (h : ∀ child ∈ children,Sparse child) :
    (combine children).length ≤ 2*cells (combine children)+children.length := by
  induction children with
  | nil => simp [combine,cells,listCells,arraySlots]
  | cons child rest ih =>
      have hc := h child (by simp)
      have hr := ih (by intro trace ht; exact h trace (by simp [ht]))
      unfold Sparse at hc
      simp only [combine,List.length_append,under_length,BinaryPRGHeapPrimitiveLifetime.cells_append,
        BinaryPRGHeapPrimitiveLifetime.cells_under,List.length_cons]
      omega

theorem children_nil : (∀ child ∈ ([] : List Trace),Sparse child) ↔ True := by simp

theorem wrap_sparse (slots frames : ℕ) (children : List Trace)
    (h : ∀ child ∈ children,Sparse child) (hSlots : children.length+1 ≤ 2*slots) :
    Sparse (wrap slots frames children) := by
  have hc := combine_bound children h
  have hCells : cells (wrap slots frames children) = slots+cells (combine children) := by
    rw [wrap,BinaryPRGHeapPrimitiveLifetime.cells_append]
    simp only [cells,listCells,arraySlots]
    omega
  unfold Sparse
  rw [hCells]
  simp only [wrap,List.length_append,List.length_cons,List.length_nil]
  omega

theorem wrapList_sparse (allocated slots frames : ℕ) (children : List Trace)
    (h : ∀ child ∈ children,Sparse child) (hSlots : children.length+2 ≤ 2*(allocated+slots)) :
    Sparse (wrapList allocated slots frames children) := by
  have hc := combine_bound children h
  have hCells : cells (wrapList allocated slots frames children) = allocated+slots+cells (combine children) := by
    rw [wrapList,BinaryPRGHeapPrimitiveLifetime.cells_append,wrap,BinaryPRGHeapPrimitiveLifetime.cells_append]
    simp only [cells,listCells,arraySlots]
    omega
  unfold Sparse
  rw [hCells]
  simp only [wrapList,wrap,List.length_append,List.length_cons,List.length_nil]
  omega

theorem prefix_one (header trace : Trace) (depth : ℕ)
    (hHeader : header.length ≤ 2*cells header) (h : Sparse trace) :
    Sparse (header++under depth trace) := by
  unfold Sparse at h ⊢
  simp only [List.length_append,under_length,BinaryPRGHeapPrimitiveLifetime.cells_append,
    BinaryPRGHeapPrimitiveLifetime.cells_under]
  omega

theorem prefix_two (header first second : Trace) (a b : ℕ)
    (hHeader : header.length+1 ≤ 2*cells header) (hFirst : Sparse first) (hSecond : Sparse second) :
    Sparse (header++under a first++under b second) := by
  unfold Sparse at hFirst hSecond ⊢
  simp only [List.length_append,under_length,BinaryPRGHeapPrimitiveLifetime.cells_append,
    BinaryPRGHeapPrimitiveLifetime.cells_under]
  omega

theorem prefix_three (header first second third : Trace) (a b c : ℕ)
    (hHeader : header.length+2 ≤ 2*cells header)
    (hFirst : Sparse first) (hSecond : Sparse second) (hThird : Sparse third) :
    Sparse (header++under a first++under b second++under c third) := by
  unfold Sparse at hFirst hSecond hThird ⊢
  simp only [List.length_append,under_length,BinaryPRGHeapPrimitiveLifetime.cells_append,
    BinaryPRGHeapPrimitiveLifetime.cells_under]
  omega

theorem reverse_sparse (bits acc : List Bool) : Sparse (reverseWithTrace bits acc).2 := by
  simp only [Sparse,BinaryResourceTraceLength.reverse_trace_length,cells,reverseWithTrace_cells,
    reverseWithTrace_arrays]
  omega

theorem scan_sparse (bits : List Bool) : Sparse (BinaryBooleanPrimitiveLifetime.scanWithTrace bits).2 := by
  induction bits with
  | nil => simp [BinaryBooleanPrimitiveLifetime.scanWithTrace,Sparse,cells,listCells,arraySlots]
  | cons bit rest ih =>
      cases bit
      · simpa only [BinaryBooleanPrimitiveLifetime.scanWithTrace,Bool.false_eq_true,ite_false] using
          prefix_one [.frames 1,.arrayAllocation 4] _ 1 (by simp [cells,listCells,arraySlots]) ih
      · simp [BinaryBooleanPrimitiveLifetime.scanWithTrace,Sparse,cells,listCells,arraySlots]

theorem carry_sparse (bits : List Bool) : Sparse (BinaryWordStoreLifetime.carryWithTrace bits).2 := by
  induction bits with
  | nil => simp [BinaryWordStoreLifetime.carryWithTrace,Sparse,cells,listCells,arraySlots]
  | cons bit rest ih =>
      cases bit with
      | false => simp [BinaryWordStoreLifetime.carryWithTrace,Sparse,cells,listCells,arraySlots]
      | true =>
          simpa only [BinaryWordStoreLifetime.carryWithTrace] using
            prefix_one [.frames 1,.listAllocation 1,.arrayAllocation 4] _ 1
              (by simp [cells,listCells,arraySlots]) ih

theorem field_sparse (bits : List Bool) : Sparse (BinaryPRGHeapPrimitiveLifetime.fieldWithTrace bits).2 := by
  induction bits with
  | nil => simp [BinaryPRGHeapPrimitiveLifetime.fieldWithTrace,Sparse,cells,listCells,arraySlots]
  | cons bit rest ih =>
      exact prefix_one [.frames 1,.arrayAllocation 8,.listAllocation 2] _ 1
        (by simp [cells,listCells,arraySlots]) ih

theorem readField_sparse (bits : List Bool) : Sparse (BinaryPRGHeapPrimitiveLifetime.readFieldWithTrace bits).2 := by
  induction bits using BinaryPRGHeapPrimitiveLifetime.readFieldWithTrace.induct with
  | case1 rest => simp [BinaryPRGHeapPrimitiveLifetime.readFieldWithTrace,Sparse,cells,listCells,arraySlots]
  | case2 bit rest ih =>
      exact prefix_one [.frames 1,.arrayAllocation 8,.listAllocation 1] _ 1
        (by simp [cells,listCells,arraySlots]) ih
  | case3 bits hFalse hTrue =>
      cases bits with
      | nil => simp [BinaryPRGHeapPrimitiveLifetime.readFieldWithTrace,Sparse,cells,listCells,arraySlots]
      | cons bit rest =>
          cases bit with
          | false => exact False.elim (hFalse rest rfl)
          | true => cases rest with
            | nil => simp [BinaryPRGHeapPrimitiveLifetime.readFieldWithTrace,Sparse,cells,listCells,arraySlots]
            | cons next tail => exact False.elim (hTrue next tail rfl)

theorem append_sparse (first second : List Bool) : Sparse (BinaryPRGHeapPrimitiveLifetime.appendWithTrace first second).2 := by
  induction first with
  | nil => simp [BinaryPRGHeapPrimitiveLifetime.appendWithTrace,Sparse,cells,listCells,arraySlots]
  | cons bit rest ih =>
      exact prefix_one [.frames 1,.arrayAllocation 8,.listAllocation 1] _ 1
        (by simp [cells,listCells,arraySlots]) ih

theorem predecessor_sparse (bits : List Bool) : Sparse (BinaryPRGHeapPrimitiveLifetime.predecessorWithTrace bits).2 := by
  induction bits with
  | nil => simp [BinaryPRGHeapPrimitiveLifetime.predecessorWithTrace,Sparse,cells,listCells,arraySlots]
  | cons bit rest ih =>
      cases bit with
      | false =>
          exact prefix_one [.frames 1,.arrayAllocation 8,.listAllocation 1] _ 1
            (by simp [cells,listCells,arraySlots]) ih
      | true => simp [BinaryPRGHeapPrimitiveLifetime.predecessorWithTrace,Sparse,cells,listCells,arraySlots]

theorem skip_sparse (tape pointer : List Bool) : Sparse (BinaryPRGHeapPrimitiveLifetime.skipWithTrace tape pointer).2 := by
  induction tape generalizing pointer with
  | nil =>
      have hs := scan_sparse pointer
      unfold BinaryPRGHeapPrimitiveLifetime.skipWithTrace
      dsimp only
      split <;> exact prefix_one [.frames 2,.arrayAllocation 8] _ 1 (by simp [cells,listCells,arraySlots]) hs
  | cons bit rest ih =>
      have hs := scan_sparse pointer
      have hd := predecessor_sparse pointer
      have hl := ih (BinaryPRGHeapPrimitiveLifetime.predecessorWithTrace pointer).1
      unfold BinaryPRGHeapPrimitiveLifetime.skipWithTrace
      dsimp only
      split
      · exact prefix_three [.frames 2,.arrayAllocation 8] _ _ _ 1 1 1
          (by simp [cells,listCells,arraySlots]) hs hd hl
      · exact prefix_one [.frames 2,.arrayAllocation 8] _ 1 (by simp [cells,listCells,arraySlots]) hs

theorem decode_sparse (bits : List Bool) : Sparse (BinaryPRGHeapAllocationLifetime.decodeWithTrace bits).2 := by
  cases bits with
  | nil => simp [BinaryPRGHeapAllocationLifetime.decodeWithTrace,Sparse,cells,listCells,arraySlots]
  | cons tag rest =>
      cases tag with
      | false => cases rest with
        | nil => simp [BinaryPRGHeapAllocationLifetime.decodeWithTrace,Sparse,cells,listCells,arraySlots]
        | cons negative rest =>
            have hf := readField_sparse rest
            unfold BinaryPRGHeapAllocationLifetime.decodeWithTrace
            dsimp only
            split
            · exact prefix_one [.frames 2,.arrayAllocation 8] _ 1 (by simp [cells,listCells,arraySlots]) hf
            · rename_i parsed hParsed
              exact prefix_two [.frames 2,.arrayAllocation 16] _ _ 1 1
                (by simp [cells,listCells,arraySlots]) hf (readField_sparse parsed.2)
      | true =>
          have hf := readField_sparse rest
          unfold BinaryPRGHeapAllocationLifetime.decodeWithTrace
          dsimp only
          split
          · exact prefix_one [.frames 2,.arrayAllocation 8] _ 1 (by simp [cells,listCells,arraySlots]) hf
          · rename_i parsed hParsed
            exact prefix_two [.frames 2,.arrayAllocation 16] _ _ 1 1
              (by simp [cells,listCells,arraySlots]) hf (readField_sparse parsed.2)

theorem read_sparse (tape pointer : List Bool) : Sparse (BinaryPRGHeapAllocationLifetime.readWithTrace tape pointer).2 := by
  exact prefix_two [.frames 2,.arrayAllocation 8] _ _ 1 1
    (by simp [cells,listCells,arraySlots]) (skip_sparse tape pointer)
    (decode_sparse (BinaryPRGHeapPrimitiveLifetime.skipWithTrace tape pointer).1)

theorem encode_sparse (cell : BinaryPRGWordStoreHeap.Cell) : Sparse (BinaryPRGHeapAllocationLifetime.encodeWithTrace cell).2 := by
  cases cell with
  | leaf word =>
      exact prefix_three [.frames 2,.arrayAllocation 8,.listAllocation 2] _ _ _ 1 1 1
        (by simp [cells,listCells,arraySlots]) (field_sparse word.numerator) (field_sparse word.denominator)
        (append_sparse (BinaryPRGHeapPrimitiveLifetime.fieldWithTrace word.numerator).1
          (BinaryPRGHeapPrimitiveLifetime.fieldWithTrace word.denominator).1)
  | branch left right =>
      exact prefix_three [.frames 2,.arrayAllocation 8,.listAllocation 1] _ _ _ 1 1 1
        (by simp [cells,listCells,arraySlots]) (field_sparse left) (field_sparse right)
        (append_sparse (BinaryPRGHeapPrimitiveLifetime.fieldWithTrace left).1
          (BinaryPRGHeapPrimitiveLifetime.fieldWithTrace right).1)

theorem count_sparse {α : Type*} (items : List α) (counter : List Bool) :
    Sparse (BinaryPRGHeapAllocationLifetime.countWithTrace items counter).2 := by
  induction items generalizing counter with
  | nil => simp [BinaryPRGHeapAllocationLifetime.countWithTrace,Sparse,cells,listCells,arraySlots]
  | cons item rest ih =>
      exact prefix_two [.frames 2,.arrayAllocation 8] _ _ 1 1 (by simp [cells,listCells,arraySlots])
        (carry_sparse counter) (ih (BinaryWordStoreLifetime.carryWithTrace counter).1)

theorem allocate_sparse (heap : BinaryPRGWordStoreHeap.Heap) (cell : BinaryPRGWordStoreHeap.Cell) :
    Sparse (BinaryPRGHeapAllocationLifetime.allocateWithTrace heap cell).2 := by
  exact prefix_three [.frames 2,.arrayAllocation 16] _ _ _ 1 1 1
    (by simp [cells,listCells,arraySlots]) (encode_sparse cell)
    (append_sparse heap.tape (BinaryPRGHeapAllocationLifetime.encodeWithTrace cell).1)
    (count_sparse (BinaryPRGHeapAllocationLifetime.encodeWithTrace cell).1 heap.next)

theorem build_sparse (fallback : SignedWord) (ruler : List Bool) (items : List SignedWord)
    (heap : BinaryPRGWordStoreHeap.Heap) :
    Sparse (BinaryPRGHeapPreparationLifetime.buildWithTrace fallback ruler items heap).2 := by
  induction ruler generalizing items heap with
  | nil =>
      cases items with
      | nil =>
          exact prefix_one [.frames 2,.arrayAllocation 16] _ 1
            (by simp [cells,listCells,arraySlots]) (allocate_sparse heap (.leaf fallback))
      | cons word rest =>
          exact prefix_one [.frames 2,.arrayAllocation 16] _ 1
            (by simp [cells,listCells,arraySlots]) (allocate_sparse heap (.leaf word))
  | cons marker ruler ih =>
      let first := BinaryPRGHeapPreparationLifetime.buildWithTrace fallback ruler items heap
      let second := BinaryPRGHeapPreparationLifetime.buildWithTrace fallback ruler first.1.remaining first.1.heap
      exact prefix_three [.frames 2,.arrayAllocation 24] _ _ _ 1 1 1
        (by simp [cells,listCells,arraySlots]) (ih items heap) (ih first.1.remaining first.1.heap)
        (allocate_sparse second.1.heap (.branch first.1.root second.1.root))

theorem ruler_prepare_sparse (fallback : SignedWord) (ruler : List Bool) (items : List SignedWord) :
    Sparse (BinaryPRGHeapRulerLifetime.prepareRulerWithTrace fallback ruler items).2 := by
  apply wrap_sparse
  · simp only [List.forall_mem_cons,children_nil,and_true]
    exact build_sparse fallback ruler items BinaryPRGWordStoreHeap.empty
  · simp only [List.length_cons,List.length_nil]; omega

theorem raw_arrays_sparse (capacity resource : List SignedWord) :
    Sparse (BinaryPhysicalHeapInputLifetime.rawArraysWithTrace capacity resource).2 := by
  unfold BinaryPhysicalHeapInputLifetime.rawArraysWithTrace
  dsimp only
  apply wrapList_sparse
  · simp only [List.forall_mem_cons,children_nil,and_true]
    exact ⟨count_sparse capacity [],ruler_prepare_sparse _ _ _,ruler_prepare_sparse _ _ _⟩
  · simp only [List.length_cons,List.length_nil]; omega

theorem reference_read_sparse (tape index : List Bool) :
    Sparse (BinaryReferenceVectorLifetime.readWithTrace tape index).2 := by
  have hf := readField_sparse tape
  unfold BinaryReferenceVectorLifetime.readWithTrace
  dsimp only
  split
  · apply wrap_sparse
    · simp only [List.forall_mem_cons,children_nil,and_true]; exact hf
    · simp only [List.length_cons,List.length_nil]; omega
  · rename_i parsed hParsed
    have hs := scan_sparse index
    split
    · have hp := predecessor_sparse index
      have hLess : parsed.2.length < tape.length :=
        BinaryReferenceVector.readField_strict tape parsed
          ((BinaryPRGWordStoreHeapMachine.readFieldWithWork_erasure tape).symm.trans
            ((BinaryPRGHeapPrimitiveLifetime.readFieldWithTrace_erasure tape).symm.trans hParsed))
      have hl := reference_read_sparse parsed.2 (BinaryPRGHeapPrimitiveLifetime.predecessorWithTrace index).1
      apply wrap_sparse
      · simp only [List.forall_mem_cons,children_nil,and_true]; exact ⟨hf,hs,hp,hl⟩
      · simp only [List.length_cons,List.length_nil]; omega
    · apply wrap_sparse
      · simp only [List.forall_mem_cons,children_nil,and_true]; exact ⟨hf,hs⟩
      · simp only [List.length_cons,List.length_nil]; omega
termination_by tape.length
decreasing_by omega

theorem object_get_sparse {n : ℕ} (store : BinaryWordObjectArray.Store n) (index : List Bool) :
    Sparse (BinaryWordObjectArrayAccess.getWithTrace store index).2 := by
  have hs := reference_read_sparse store.slots index
  unfold BinaryWordObjectArrayAccess.getWithTrace
  dsimp only
  split
  · apply wrap_sparse
    · simp only [List.forall_mem_cons,children_nil,and_true]; exact hs
    · simp only [List.length_cons,List.length_nil]; omega
  · rename_i pointer hPointer
    apply wrap_sparse
    · simp only [List.forall_mem_cons,children_nil,and_true]
      exact ⟨hs,read_sparse store.heap.tape pointer⟩
    · simp only [List.length_cons,List.length_nil]; omega

theorem index_loop_sparse {α : Type*} (ruler : List α) (counter : List Bool) :
    Sparse (BooleanArrayIndexEnumeration.loopWithTrace ruler counter).2 := by
  induction ruler generalizing counter with
  | nil => exact wrap_sparse 8 1 [] (by simp) (by simp only [List.length_cons,List.length_nil]; omega)
  | cons item rest ih =>
      apply wrapList_sparse
      · simp only [List.forall_mem_cons,children_nil,and_true]
        exact ⟨carry_sparse counter,ih (BinaryWordStoreLifetime.carryWithTrace counter).1⟩
      · simp only [List.length_cons,List.length_nil]; omega

theorem indices_sparse {α : Type*} (ruler : List α) :
    Sparse (BooleanArrayIndexEnumeration.enumerateWithTrace ruler).2 :=
  index_loop_sparse ruler []

theorem read_many_sparse {n : ℕ} (store : BinaryWordObjectArray.Store n) (indices : List (List Bool)) :
    Sparse (BinaryPhysicalNumericalReadbackLifetime.readManyWithTraceAndWork store indices).1.2 := by
  induction indices with
  | nil => exact wrap_sparse 8 1 [] (by simp) (by simp only [List.length_cons,List.length_nil]; omega)
  | cons index rest ih =>
      unfold BinaryPhysicalNumericalReadbackLifetime.readManyWithTraceAndWork
      dsimp only
      apply wrapList_sparse
      · simp only [List.forall_mem_cons,children_nil,and_true]; exact ⟨object_get_sparse store index,ih⟩
      · simp only [List.length_cons,List.length_nil]; omega

theorem read_all_sparse {n : ℕ} (store : BinaryWordObjectArray.Store n) :
    Sparse (BinaryPhysicalNumericalReadbackLifetime.readAllWithTraceAndWork store).1.2 := by
  unfold BinaryPhysicalNumericalReadbackLifetime.readAllWithTraceAndWork
  dsimp only
  apply wrap_sparse
  · simp only [List.forall_mem_cons,children_nil,and_true]
    exact ⟨indices_sparse (List.finRange n),read_many_sparse store _⟩
  · simp only [List.length_cons,List.length_nil]; omega

theorem read_pair_sparse {n : ℕ} (request : BinaryPRGPhysicalRawRequestLifetime.Request n) :
    Sparse (BinaryPhysicalNumericalReadbackLifetime.readPairWithTraceAndWork request).1.2 := by
  unfold BinaryPhysicalNumericalReadbackLifetime.readPairWithTraceAndWork
  dsimp only
  apply wrap_sparse
  · simp only [List.forall_mem_cons,children_nil,and_true]
    exact ⟨read_all_sparse request.physical.lengthStore,read_all_sparse request.physical.poorStore⟩
  · simp only [List.length_cons,List.length_nil]; omega

theorem lookup_sparse (tape pointer ruler address : List Bool) :
    Sparse (BinaryPRGHeapAccessLifetime.lookupWithTrace tape pointer ruler address).2 := by
  induction ruler generalizing pointer address with
  | nil =>
      exact prefix_one [.frames 2,.arrayAllocation 8] _ 1
        (by simp [cells,listCells,arraySlots]) (read_sparse tape pointer)
  | cons marker ruler ih =>
      have hf := read_sparse tape pointer
      unfold BinaryPRGHeapAccessLifetime.lookupWithTrace
      dsimp only
      cases hFound : (BinaryPRGHeapAllocationLifetime.readWithTrace tape pointer).1 with
      | none =>
          simp only [hFound]
          exact prefix_one [.frames 2,.arrayAllocation 8] _ 1 (by simp [cells,listCells,arraySlots]) hf
      | some cell => cases cell with
        | leaf word =>
            simp only [hFound]
            exact prefix_one [.frames 2,.arrayAllocation 8] _ 1 (by simp [cells,listCells,arraySlots]) hf
        | branch left right =>
            simp only [hFound]
            split
            · exact prefix_two [.frames 2,.arrayAllocation 8] _ _ 1 1
                (by simp [cells,listCells,arraySlots]) hf (ih right address.tail)
            · exact prefix_two [.frames 2,.arrayAllocation 8] _ _ 1 1
                (by simp [cells,listCells,arraySlots]) hf (ih left address.tail)

theorem packed_read_sparse {depth : ℕ} (data : BinaryPRGHeapPackedStore.Packed depth) (address : FixedBinaryWord depth) :
    Sparse (BinaryHeapPackedReadMeasured.read data address).1.2 := by
  rw [BinaryHeapPackedReadMeasured.read_erases]
  exact prefix_two [.frames 2,.arrayAllocation 16] _ _ 1 1
    (by simp [cells,listCells,arraySlots]) (reverse_sparse address.bits [])
    (lookup_sparse data.heap.tape data.root data.ruler (reverseWithTrace address.bits []).1)

theorem comparison_sparse (first second : SignedWord) :
    Sparse (BinaryRationalComparisonMeasured.traced first second).1.2 := by
  simp only [Sparse,BinaryRationalComparisonMeasured.traced,cells,listCells,arraySlots,
    List.length_cons,List.length_nil]
  omega

open BinaryPRGWordControllerWordStore (Store)
open BinaryPRGHeapStoredTree (Stored)
open BinaryPRGWordControllerBooleanResourceUpdate (Address)
variable {capacity : Store}

theorem fractional_sparse (limits : Stored capacity.tree) (bids : BinaryPRGHeapPackedStore.Packed capacity.width)
    (address : Address capacity.width capacity.cap) :
    Sparse (BinaryHeapScanMeasured.fractional limits bids address).1.2 := by
  unfold BinaryHeapScanMeasured.fractional
  dsimp only
  apply wrap_sparse
  · simp only [List.forall_mem_cons,children_nil,and_true]
    exact ⟨packed_read_sparse _ _,packed_read_sparse _ _,comparison_sparse _ _,comparison_sparse _ _⟩
  · simp only [List.length_cons,List.length_nil]; omega

theorem heap_scan_sparse (limits : Stored capacity.tree) (bids : BinaryPRGHeapPackedStore.Packed capacity.width)
    (addresses : List (Address capacity.width capacity.cap)) :
    Sparse (BinaryHeapScanMeasured.scan limits bids addresses).1.2 := by
  induction addresses with
  | nil => exact wrap_sparse 8 1 [] (by simp) (by simp only [List.length_cons,List.length_nil]; omega)
  | cons address rest ih =>
      unfold BinaryHeapScanMeasured.scan
      dsimp only
      apply wrapList_sparse
      · simp only [List.forall_mem_cons,children_nil,and_true]; exact ⟨fractional_sparse limits bids address,ih⟩
      · simp only [List.length_cons,List.length_nil]; omega

theorem increment_bits_sparse (bits : List Bool) : Sparse (BinaryWordStoreLifetime.incrementBitsWithTrace bits).2 := by
  induction bits with
  | nil => simp [BinaryWordStoreLifetime.incrementBitsWithTrace,Sparse,cells,listCells,arraySlots]
  | cons bit rest ih =>
      cases bit with
      | false => simp [BinaryWordStoreLifetime.incrementBitsWithTrace,Sparse,cells,listCells,arraySlots]
      | true =>
          exact prefix_one [.frames 1,.listAllocation 1,.arrayAllocation 4] _ 1
            (by simp [cells,listCells,arraySlots]) ih

theorem increment_sparse {w : ℕ} (word : FixedBinaryWord w) : Sparse (BinaryWordStoreLifetime.incrementWithTrace word).2 := by
  exact prefix_one [.frames 2,.arrayAllocation 8] _ 2 (by simp [cells,listCells,arraySlots]) (increment_bits_sparse word.bits)

theorem guard_sparse {w : ℕ} (first second : FixedBinaryWord w) : Sparse (BinaryWordStoreLifetime.ltWithTrace first second).2 := by
  simp only [BinaryWordStoreLifetime.ltWithTrace,Sparse,cells,listCells,arraySlots,List.length_cons,List.length_nil]
  omega

theorem enumerate_sparse {w : ℕ} (cap pc : FixedBinaryWord w) (hp : pc.value ≤ cap.value) :
    Sparse (BinaryPRGHeapEnumerationLifetime.enumerateWithTrace cap pc hp).2 := by
  unfold BinaryPRGHeapEnumerationLifetime.enumerateWithTrace
  dsimp only
  have hg := guard_sparse pc cap
  split
  · rename_i hRead
    have hLt : pc.value < cap.value := (BinaryIndexWord.lt_value pc cap).mp
      ((BinaryWordStoreLifetime.ltWithTrace_erases pc cap).symm.trans hRead)
    have hNext : (BinaryWordStoreLifetime.incrementWithTrace pc).1.1.value = pc.value+1 := by
      rw [BinaryWordStoreLifetime.incrementWithTrace_erases]
      exact (BinaryIndexWord.increment_value pc (by have h := BinaryPRGHeapAddressEnumeration.cap_room cap; omega)).1
    have hpNext : (BinaryWordStoreLifetime.incrementWithTrace pc).1.1.value ≤ cap.value := by omega
    have hLess : cap.value-(BinaryWordStoreLifetime.incrementWithTrace pc).1.1.value < cap.value-pc.value := by omega
    have hl := enumerate_sparse cap (BinaryWordStoreLifetime.incrementWithTrace pc).1.1 hpNext
    apply wrapList_sparse
    · simp only [List.forall_mem_cons,children_nil,and_true]; exact ⟨hg,increment_sparse pc,hl⟩
    · simp only [List.length_cons,List.length_nil]; omega
  · apply wrap_sparse
    · simp only [List.forall_mem_cons,children_nil,and_true]; exact hg
    · simp only [List.length_cons,List.length_nil]; omega
termination_by cap.value-pc.value
decreasing_by omega

theorem allFromBits_sparse {w : ℕ} (cap : FixedBinaryWord w) :
    Sparse (BinaryHeapEnumerationWidthMeasured.allFromBits cap).1.2 := by
  rw [BinaryHeapEnumerationWidthMeasured.allFromBits_erases,
    BinaryPRGHeapEnumerationLifetime.allFromBitsWithTrace_eq]
  unfold BinaryPRGHeapEnumerationLifetime.allWithTrace
  dsimp only
  apply wrapList_sparse
  · simp only [List.forall_mem_cons,children_nil,and_true]; exact enumerate_sparse _ _ _
  · simp only [List.length_cons,List.length_nil]; omega

theorem measured_reverse_sparse (bits acc : List Bool) : Sparse (BinarySeedCursorMeasured.reverse bits acc).1.2 := by
  rw [BinarySeedCursorMeasured.reverse_erases]
  exact reverse_sparse bits acc

theorem allowance_addLoop_sparse (a b : List Bool) (carry : Bool) (acc : List Bool) :
    Sparse (BinaryBuildAllowanceArithmeticMeasured.addLoop a b carry acc).1.2 := by
  induction a generalizing b carry acc with
  | nil =>
      induction b generalizing carry acc with
      | nil =>
          unfold BinaryBuildAllowanceArithmeticMeasured.addLoop
          dsimp only
          apply wrapList_sparse
          · simp only [List.forall_mem_cons,children_nil,and_true]; exact measured_reverse_sparse _ _
          · simp only [List.length_cons,List.length_nil]; omega
      | cons bit rest ih =>
          unfold BinaryBuildAllowanceArithmeticMeasured.addLoop
          dsimp only
          apply wrapList_sparse
          · simp only [List.forall_mem_cons,children_nil,and_true]; exact ih _ _
          · simp only [List.length_cons,List.length_nil]; omega
  | cons bit rest ih =>
      cases b with
      | nil =>
          unfold BinaryBuildAllowanceArithmeticMeasured.addLoop
          dsimp only
          apply wrapList_sparse
          · simp only [List.forall_mem_cons,children_nil,and_true]; exact ih [] _ _
          · simp only [List.length_cons,List.length_nil]; omega
      | cons other tail =>
          unfold BinaryBuildAllowanceArithmeticMeasured.addLoop
          dsimp only
          apply wrapList_sparse
          · simp only [List.forall_mem_cons,children_nil,and_true]; exact ih tail _ _
          · simp only [List.length_cons,List.length_nil]; omega

theorem allowance_add_sparse (a b : List Bool) : Sparse (BinaryBuildAllowanceArithmeticMeasured.add a b).1.2 :=
  allowance_addLoop_sparse a b false []

theorem allowance_multiply_sparse (a b : List Bool) : Sparse (BinaryBuildAllowanceArithmeticMeasured.multiply a b).1.2 := by
  induction a with
  | nil => exact wrap_sparse 8 1 [] (by simp) (by simp only [List.length_cons,List.length_nil]; omega)
  | cons bit rest ih =>
      unfold BinaryBuildAllowanceArithmeticMeasured.multiply
      dsimp only
      split
      · apply wrapList_sparse
        · simp only [List.forall_mem_cons,children_nil,and_true]; exact ⟨ih,allowance_add_sparse _ _⟩
        · simp only [List.length_cons,List.length_nil]; omega
      · apply wrapList_sparse
        · simp only [List.forall_mem_cons,children_nil,and_true]; exact ih
        · simp only [List.length_cons,List.length_nil]; omega

theorem allowance_nodes_sparse (ruler : List Bool) : Sparse (BinaryBuildAllowanceArithmeticMeasured.nodes ruler).1.2 := by
  induction ruler with
  | nil => exact wrapList_sparse 1 8 1 [] (by simp) (by simp only [List.length_cons,List.length_nil]; omega)
  | cons marker rest ih =>
      apply wrapList_sparse
      · simp only [List.forall_mem_cons,children_nil,and_true]; exact ih
      · simp only [List.length_cons,List.length_nil]; omega

theorem allowance_tree_sparse (nodes tape : List Bool) : Sparse (BinaryPhysicalBuildAllowanceMeasured.tree nodes tape).1.2 := by
  unfold BinaryPhysicalBuildAllowanceMeasured.tree
  dsimp only
  apply wrapList_sparse
  · simp only [List.forall_mem_cons,children_nil,and_true]
    refine ⟨?_,allowance_multiply_sparse _ _,allowance_multiply_sparse _ _,allowance_add_sparse _ _,allowance_multiply_sparse _ _⟩
    rw [BinaryHeapAllocationMeasured.count_erases]
    exact count_sparse tape [true]
  · simp only [List.length_cons,List.length_nil]; omega

theorem allowance_calculate_sparse (ruler first second : List Bool) :
    Sparse (BinaryPhysicalBuildAllowanceMeasured.calculate ruler first second).1.2 := by
  unfold BinaryPhysicalBuildAllowanceMeasured.calculate
  dsimp only
  apply wrap_sparse
  · simp only [List.forall_mem_cons,children_nil,and_true]
    exact ⟨allowance_nodes_sparse ruler,allowance_tree_sparse _ first,allowance_tree_sparse _ second,allowance_add_sparse _ _⟩
  · simp only [List.length_cons,List.length_nil]; omega

variable {n : ℕ}

theorem initial_arrays_sparse (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j))
    (built : BinaryPRGHeapInitialLifetime.ArraysAt capacity resource
      (BinaryCarryCounter.count capacity.data.toList []))
    (hBuilt : built = (BinaryPRGHeapInitialLifetime.arraysWithTrace capacity resource).1)
    (trace : Trace) (hTrace : Sparse trace) :
    Sparse (BinaryPhysicalHeapInitialLifetime.initialFromArraysWithTraceAndWork
      capacity resource hC hR built hBuilt trace).1.2 := by
  unfold BinaryPhysicalHeapInitialLifetime.initialFromArraysWithTraceAndWork
  dsimp only
  apply wrap_sparse
  · simp only [List.forall_mem_cons,children_nil,and_true]
    exact ⟨hTrace,allFromBits_sparse _,heap_scan_sparse _ _ _⟩
  · simp only [List.length_cons,List.length_nil]; omega

theorem initial_words_sparse (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j))
    (capacityWords resourceWords : List SignedWord)
    (hCapacity : capacityWords = capacity.data.toList) (hResource : resourceWords = resource.data.toList)
    (readTrace : Trace) (hReadTrace : Sparse readTrace) :
    Sparse (BinaryPhysicalHeapAllowanceInitial.initialFromWords capacity resource hC hR
      capacityWords resourceWords hCapacity hResource readTrace).1.2 := by
  unfold BinaryPhysicalHeapAllowanceInitial.initialFromWords
  dsimp only
  apply wrap_sparse
  · simp only [List.forall_mem_cons,children_nil,and_true]
    refine ⟨hReadTrace,?_⟩
    apply initial_arrays_sparse
    apply wrap_sparse
    · simp only [List.forall_mem_cons,children_nil,and_true]
      exact ⟨raw_arrays_sparse capacityWords resourceWords,allowance_calculate_sparse _ _ _⟩
    · simp only [List.length_cons,List.length_nil]; omega
  · simp only [List.length_cons,List.length_nil]; omega

theorem initial_sparse (request : BinaryPRGPhysicalRawRequestLifetime.Request n) (rich : Bool) :
    Sparse (BinaryPhysicalHeapAllowanceInitial.initialFromRequest request rich).1.2 := by
  unfold BinaryPhysicalHeapAllowanceInitial.initialFromRequest
  dsimp only
  apply initial_words_sparse
  exact read_pair_sparse request

theorem sparse_length_usage (trace : Trace) (h : Sparse trace) : trace.length ≤ 2*usage trace+1 := by
  unfold Sparse at h
  unfold usage
  omega

theorem initial_length_usage (request : BinaryPRGPhysicalRawRequestLifetime.Request n) (rich : Bool) :
    (BinaryPhysicalHeapAllowanceInitial.initialFromRequest request rich).1.2.length ≤
      2*usage (BinaryPhysicalHeapAllowanceInitial.initialFromRequest request rich).1.2+1 :=
  sparse_length_usage _ (initial_sparse request rich)

theorem accepted_initial_length : ∃ C d : ℕ,
    ∀ (frame : List Bool) (parsed : (Σ n,BinaryPRGPhysicalRawRequestLifetime.Request n) × List Bool),
      (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed → ∀ rich : Bool,
        (BinaryPhysicalHeapAllowanceInitial.initialFromRequest parsed.1.2 rich).1.2.length ≤ C*(frame.length+3)^d := by
  obtain ⟨C₁,d₁,hOld⟩ := BinaryPhysicalHeapRequestLifetime.accepted_physical_initial_trace_polynomial
  obtain ⟨C₂,d₂,hCalc⟩ := BinaryPhysicalHeapAllowanceInitial.accepted_calculationTrace_polynomial
  refine ⟨2*C₁+2*C₂+77,max d₁ d₂,?_⟩
  intro frame parsed hParsed rich
  let x := frame.length+3
  let D := max d₁ d₂
  have hx : 0 < x := by dsimp only [x]; omega
  have hJ := initial_length_usage parsed.1.2 rich
  have hUsage := BinaryPhysicalHeapAllowanceInitial.initialFromRequest_usage parsed.1.2 rich
  have ho := hOld frame parsed hParsed rich
  change usage (BinaryPhysicalHeapInitialLifetime.initialFromRequestWithTraceAndWork parsed.1.2 rich).1.2 ≤
    C₁*x^d₁ at ho
  have hc := hCalc frame parsed hParsed rich
  dsimp only at hc hUsage
  have hp₁ : x^d₁ ≤ x^D := Nat.pow_le_pow_right hx (Nat.le_max_left _ _)
  have hp₂ : x^d₂ ≤ x^D := Nat.pow_le_pow_right hx (Nat.le_max_right _ _)
  have h₁ := Nat.mul_le_mul_left C₁ hp₁
  have h₂ := Nat.mul_le_mul_left C₂ hp₂
  have hOne : 1 ≤ x^D := Nat.one_le_pow D x hx
  change (BinaryPhysicalHeapAllowanceInitial.initialFromRequest parsed.1.2 rich).1.2.length ≤
    (2*C₁+2*C₂+77)*x^D
  calc
    _ ≤ 2*(C₁*x^D)+2*(C₂*x^D)+77 := by
      dsimp only [x] at *
      omega
    _ ≤ 2*(C₁*x^D)+2*(C₂*x^D)+77*x^D := by omega
    _ = (2*C₁+2*C₂+77)*x^D := by ring

theorem accepted_initial_overhead : ∃ C d : ℕ,
    ∀ (frame : List Bool) (parsed : (Σ n,BinaryPRGPhysicalRawRequestLifetime.Request n) × List Bool),
      (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed → ∀ rich : Bool,
        5*(BinaryPhysicalHeapAllowanceInitial.initialFromRequest parsed.1.2 rich).1.2.length+
          16*parsed.1.1+20 ≤ C*(frame.length+3)^d := by
  obtain ⟨C,d,hInitial⟩ := accepted_initial_length
  refine ⟨5*C+36,max d 1,?_⟩
  intro frame parsed hParsed rich
  let x := frame.length+3
  let D := max d 1
  have hx : 0 < x := by dsimp only [x]; omega
  have hJ := hInitial frame parsed hParsed rich
  have hn := BinaryPhysicalNumericalReadbackLifetime.accepted_dimension frame parsed hParsed
  have hp : x^d ≤ x^D := Nat.pow_le_pow_right hx (Nat.le_max_left _ _)
  have hPow := Nat.mul_le_mul_left C hp
  have hX : x ≤ x^D := by
    have h := Nat.pow_le_pow_right hx (Nat.le_max_right d 1)
    simpa only [pow_one] using h
  have hOne : 1 ≤ x^D := Nat.one_le_pow D x hx
  change 5*(BinaryPhysicalHeapAllowanceInitial.initialFromRequest parsed.1.2 rich).1.2.length+
    16*parsed.1.1+20 ≤ (5*C+36)*x^D
  calc
    _ ≤ 5*(C*x^D)+16*x^D+20*x^D := by
      dsimp only [x] at *
      omega
    _ = (5*C+36)*x^D := by ring

theorem accepted_source_emission : ∃ C d : ℕ,
    ∀ (frame : List Bool) (parsed : (Σ n,BinaryPRGPhysicalRawRequestLifetime.Request n) × List Bool),
      (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed →
      ∀ (seed : BinarySeedLookupTree.Store) (rich : Bool)
        (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value),
        (BinaryPhysicalHeapAllowanceInitial.sourceAtTraceMeasured seed parsed.1.2 rich pc hp).2 ≤
          60*(BinaryPhysicalHeapAllowanceInitial.sourceAt seed parsed.1.2 rich pc hp).2+C*(frame.length+3)^d := by
  obtain ⟨C,d,hOverhead⟩ := accepted_initial_overhead
  refine ⟨C,d,?_⟩
  intro frame parsed hParsed seed rich pc hp
  have h := BinaryResourceTraceLength.source_emission seed parsed.1.2 rich pc hp
  have hb := hOverhead frame parsed hParsed rich
  omega

theorem accepted_source_total : ∃ C d : ℕ,
    ∀ (frame : List Bool) (parsed : (Σ n,BinaryPRGPhysicalRawRequestLifetime.Request n) × List Bool),
      (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed →
      ∀ (seed : BinarySeedLookupTree.Store) (rich : Bool)
        (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value),
        (BinaryPhysicalHeapAllowanceInitial.sourceAt seed parsed.1.2 rich pc hp).2+
          (BinaryPhysicalHeapAllowanceInitial.sourceAtMeasured seed parsed.1.2 rich pc hp).2+
          (BinaryPhysicalHeapAllowanceInitial.sourceAtTraceMeasured seed parsed.1.2 rich pc hp).2 ≤
            66*(BinaryPhysicalHeapAllowanceInitial.sourceAt seed parsed.1.2 rich pc hp).2+C*(frame.length+3)^d := by
  obtain ⟨C,d,hOverhead⟩ := accepted_initial_overhead
  refine ⟨C,d,?_⟩
  intro frame parsed hParsed seed rich pc hp
  have h := BinaryResourceTraceLength.source_total seed parsed.1.2 rich pc hp
  have hb := hOverhead frame parsed hParsed rich
  omega

theorem accepted_native_total : ∃ C d : ℕ,
    ∀ (frame : List Bool) (parsed : (Σ n,BinaryPRGPhysicalRawRequestLifetime.Request n) × List Bool),
      (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed →
      ∀ (seed : BinarySeedLookupTree.Store) (rich : Bool)
        (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value),
        (BinaryPhysicalHeapAllowanceRequest.nativeAt seed parsed.1.2 rich pc hp).2+
          (BinaryPhysicalHeapAllowanceRequest.nativeAtMeasured seed parsed.1.2 rich pc hp).2.1+
          (BinaryPhysicalHeapAllowanceRequest.nativeAtMeasured seed parsed.1.2 rich pc hp).2.2 ≤
            66*(BinaryPhysicalHeapAllowanceRequest.nativeAt seed parsed.1.2 rich pc hp).2+C*(frame.length+3)^d := by
  obtain ⟨C,d,hOverhead⟩ := accepted_initial_overhead
  refine ⟨C,d,?_⟩
  intro frame parsed hParsed seed rich pc hp
  have h := BinaryResourceTraceLength.native_total seed parsed.1.2 rich pc hp
  have hb := hOverhead frame parsed hParsed rich
  omega

theorem accepted_source_emission_width : ∃ C d : ℕ,
    ∀ (frame : List Bool) (parsed : (Σ n,BinaryPRGPhysicalRawRequestLifetime.Request n) × List Bool),
      (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed →
      ∀ (seed : BinarySeedLookupTree.Store) (rich : Bool)
        (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value),
        binaryWordWidth (BinaryPhysicalHeapAllowanceInitial.sourceAtTraceMeasured seed parsed.1.2 rich pc hp).2 ≤
          binaryWordWidth (60*(BinaryPhysicalHeapAllowanceInitial.sourceAt seed parsed.1.2 rich pc hp).2+C*(frame.length+3)^d) := by
  obtain ⟨C,d,hBound⟩ := accepted_source_emission
  exact ⟨C,d,fun frame parsed hParsed seed rich pc hp =>
    binaryWordWidth_mono (hBound frame parsed hParsed seed rich pc hp)⟩

end Blotto.BinaryInitialTraceSparsity
