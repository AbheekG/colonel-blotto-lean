import Blotto.BinaryHeapTapeMeasured
import Blotto.BinaryWordStoreMeasured

/-! Encoding, carry-address advancement and heap allocation produce data,
traces and conservative copied-bit/work charges in one pass. Their charges
equal the existing heap-machine model, including width/copy reservations.
Native evaluation of these observer reservations is a separate obligation. -/

namespace Blotto.BinaryHeapAllocationMeasured
open BinaryRationalNormalization BinaryPRGWordStoreHeap BinarySeedPreparationSpace
open BinaryPRGHeapTraceUsage BinaryTraceDepth
open BinaryPRGWordStoreHeapMachine (Charge)
open BinaryHeapTapeMeasured (field append field_erases append_erases field_data append_data
  field_charge append_charge)
set_option autoImplicit false
set_option maxHeartbeats 2000000

def encodeAt : Cell → ℕ → (List Bool × Trace) × Charge
  | .leaf word,depth =>
      let first := BinaryHeapTapeMeasured.fieldAt word.numerator (depth+1)
      let second := BinaryHeapTapeMeasured.fieldAt word.denominator (depth+1)
      let joined := BinaryHeapTapeMeasured.appendAt first.1.1 second.1.1 (depth+1)
      ((false::word.negative::joined.1.1,.frames (depth+2)::.arrayAllocation 8::.listAllocation 2::
        (first.1.2++(second.1.2++joined.1.2))),
        ⟨first.2.work+second.2.work+joined.2.work+4,
          first.2.allocatedBits+second.2.allocatedBits+joined.2.allocatedBits+2⟩)
  | .branch left right,depth =>
      let first := BinaryHeapTapeMeasured.fieldAt left (depth+1)
      let second := BinaryHeapTapeMeasured.fieldAt right (depth+1)
      let joined := BinaryHeapTapeMeasured.appendAt first.1.1 second.1.1 (depth+1)
      ((true::joined.1.1,.frames (depth+2)::.arrayAllocation 8::.listAllocation 1::
        (first.1.2++(second.1.2++joined.1.2))),
        ⟨first.2.work+second.2.work+joined.2.work+3,
          first.2.allocatedBits+second.2.allocatedBits+joined.2.allocatedBits+1⟩)


theorem encodeAt_erases (cell : Cell) (depth : ℕ) :
    (encodeAt cell depth).1 = ((BinaryPRGHeapAllocationLifetime.encodeWithTrace cell).1,
      under depth (BinaryPRGHeapAllocationLifetime.encodeWithTrace cell).2) := by
  cases cell <;> simp only [encodeAt,BinaryPRGHeapAllocationLifetime.encodeWithTrace,
    BinaryHeapTapeMeasured.fieldAt_erases,BinaryHeapTapeMeasured.appendAt_erases,
    under_append,under_compose,List.append_assoc] <;> rfl

def encode (cell : Cell) : (List Bool × Trace) × Charge := encodeAt cell 0

theorem encode_erases (cell : Cell) :
    (encode cell).1 = BinaryPRGHeapAllocationLifetime.encodeWithTrace cell := by
  rw [encode,encodeAt_erases,under_zero]

theorem encode_data (cell : Cell) :
    (encode cell).1.1 = (BinaryPRGWordStoreHeapMachine.encodeWithWork cell).1 := by
  have h := congrArg Prod.fst (encode_erases cell)
  exact h.trans (BinaryPRGHeapAllocationLifetime.encodeWithTrace_erasure cell)

theorem encodeAt_charge (cell : Cell) (depth : ℕ) :
    (encodeAt cell depth).2 = (BinaryPRGWordStoreHeapMachine.encodeWithWork cell).2 := by
  cases cell <;> simp only [encodeAt,BinaryPRGWordStoreHeapMachine.encodeWithWork,
    BinaryHeapTapeMeasured.fieldAt_erases,BinaryPRGHeapPrimitiveLifetime.fieldWithTrace_erasure,
    BinaryHeapTapeMeasured.fieldAt_charge,BinaryHeapTapeMeasured.appendAt_charge]

theorem encode_charge (cell : Cell) :
    (encode cell).2 = (BinaryPRGWordStoreHeapMachine.encodeWithWork cell).2 := encodeAt_charge cell 0

def countAt {α : Type*} : List α → Pointer → ℕ → (Pointer × Trace) × Charge
  | [],counter,depth => ((counter,[.frames (depth+1),.arrayAllocation 8]),⟨1,0⟩)
  | _::rest,counter,depth =>
      let advanced := BinaryWordStoreMeasured.carryAt counter (depth+1)
      let later := countAt rest advanced.1.1 (depth+1)
      ((later.1.1,.frames (depth+2)::.arrayAllocation 8::(advanced.1.2++later.1.2)),
        ⟨advanced.2+4*(counter.length+1)+later.2.work+4,
          advanced.1.1.length+later.2.allocatedBits⟩)

theorem countAt_erases {α : Type*} (items : List α) (counter : Pointer) (depth : ℕ) :
    (countAt items counter depth).1 = ((BinaryPRGHeapAllocationLifetime.countWithTrace items counter).1,
      under depth (BinaryPRGHeapAllocationLifetime.countWithTrace items counter).2) := by
  induction items generalizing counter depth with
  | nil => rfl
  | cons item rest ih =>
      simp only [countAt,BinaryPRGHeapAllocationLifetime.countWithTrace,
        BinaryWordStoreMeasured.carryAt_erases,ih,under_append,under_compose,List.append_assoc]
      rfl

def count {α : Type*} (items : List α) (counter : Pointer) : (Pointer × Trace) × Charge :=
  countAt items counter 0

theorem count_erases {α : Type*} (items : List α) (counter : Pointer) :
    (count items counter).1 = BinaryPRGHeapAllocationLifetime.countWithTrace items counter := by
  rw [count,countAt_erases,under_zero]

theorem count_data {α : Type*} (items : List α) (counter : Pointer) :
    (count items counter).1.1 = (BinaryPRGWordStoreHeapMachine.countWithWork items counter).1 := by
  have h := congrArg Prod.fst (count_erases items counter)
  exact h.trans (BinaryPRGHeapAllocationLifetime.countWithTrace_erasure items counter)

theorem countAt_charge {α : Type*} (items : List α) (counter : Pointer) (depth : ℕ) :
    (countAt items counter depth).2 = (BinaryPRGWordStoreHeapMachine.countWithWork items counter).2 := by
  induction items generalizing counter depth with
  | nil => rfl
  | cons item rest ih => simp only [countAt,BinaryPRGWordStoreHeapMachine.countWithWork,ih,
      BinaryWordStoreMeasured.carryAt_work,BinaryWordStoreWork.carry_work,
      BinaryWordStoreMeasured.carryAt_erases,BinaryWordStoreLifetime.carryWithTrace_erases]

theorem count_charge {α : Type*} (items : List α) (counter : Pointer) :
    (count items counter).2 = (BinaryPRGWordStoreHeapMachine.countWithWork items counter).2 := countAt_charge items counter 0

def allocateAt (heap : Heap) (cell : Cell) (depth : ℕ) : ((Pointer × Heap) × Trace) × Charge :=
  let encoded := encodeAt cell (depth+1)
  let written := BinaryHeapTapeMeasured.appendAt heap.tape encoded.1.1 (depth+1)
  let advanced := countAt encoded.1.1 heap.next (depth+1)
  (((heap.next,⟨written.1.1,advanced.1.1⟩),.frames (depth+2)::.arrayAllocation 16::
    (encoded.1.2++(written.1.2++advanced.1.2))),
    ⟨encoded.2.work+written.2.work+advanced.2.work+4*(heap.next.length+1)+6,
      encoded.2.allocatedBits+written.2.allocatedBits+advanced.2.allocatedBits+heap.next.length+4⟩)

theorem allocateAt_erases (heap : Heap) (cell : Cell) (depth : ℕ) :
    (allocateAt heap cell depth).1 = ((BinaryPRGHeapAllocationLifetime.allocateWithTrace heap cell).1,
      under depth (BinaryPRGHeapAllocationLifetime.allocateWithTrace heap cell).2) := by
  simp only [allocateAt,BinaryPRGHeapAllocationLifetime.allocateWithTrace,encodeAt_erases,
    BinaryHeapTapeMeasured.appendAt_erases,countAt_erases,under_append,under_compose,List.append_assoc]
  rfl

def allocate (heap : Heap) (cell : Cell) : ((Pointer × Heap) × Trace) × Charge := allocateAt heap cell 0

theorem allocate_erases (heap : Heap) (cell : Cell) :
    (allocate heap cell).1 = BinaryPRGHeapAllocationLifetime.allocateWithTrace heap cell := by
  rw [allocate,allocateAt_erases,under_zero]

theorem allocate_data (heap : Heap) (cell : Cell) :
    (allocate heap cell).1.1 = (BinaryPRGWordStoreHeapMachine.allocateWithWork heap cell).1 := by
  have h := congrArg Prod.fst (allocate_erases heap cell)
  exact h.trans (BinaryPRGHeapAllocationLifetime.allocateWithTrace_erasure heap cell)

theorem allocateAt_charge (heap : Heap) (cell : Cell) (depth : ℕ) :
    (allocateAt heap cell depth).2 = (BinaryPRGWordStoreHeapMachine.allocateWithWork heap cell).2 := by
  simp only [allocateAt,BinaryPRGWordStoreHeapMachine.allocateWithWork,
    encodeAt_erases,BinaryPRGHeapAllocationLifetime.encodeWithTrace_erasure,
    BinaryHeapTapeMeasured.appendAt_erases,BinaryPRGHeapPrimitiveLifetime.appendWithTrace_erasure,
    countAt_erases,BinaryPRGHeapAllocationLifetime.countWithTrace_erasure,
    encodeAt_charge,BinaryHeapTapeMeasured.appendAt_charge,countAt_charge]

theorem allocate_charge (heap : Heap) (cell : Cell) :
    (allocate heap cell).2 = (BinaryPRGWordStoreHeapMachine.allocateWithWork heap cell).2 := allocateAt_charge heap cell 0

theorem allocate_bound (heap : Heap) (cell : Cell) (hHeap : Valid heap) (B : ℕ)
    (hB : heap.tape.length+(BinaryPRGWordStoreHeap.encode cell).length ≤ B) :
    (allocate heap cell).2.work ≤ BinaryPRGWordStoreHeapMachine.allocationBound B ∧
      (allocate heap cell).2.allocatedBits ≤ BinaryPRGWordStoreHeapMachine.allocationBound B := by
  rw [allocate_charge]
  exact BinaryPRGWordStoreHeapMachine.allocateWithWork_bounds heap cell hHeap B hB

theorem allocate_all_prefix (heap : Heap) (cell : Cell) (hHeap : Valid heap) (B : ℕ)
    (hB : heap.tape.length+(BinaryPRGWordStoreHeap.encode cell).length ≤ B)
    (borrowed steps : ℕ) :
    retainedHeap borrowed (allocate heap cell).1.2 steps ≤
        borrowed+32*BinaryPRGWordStoreHeapMachine.allocationBound B ∧
      framePeak ((allocate heap cell).1.2.take steps) ≤ BinaryPRGWordStoreHeapMachine.allocationBound B := by
  rw [allocate_erases]
  exact BinaryPRGHeapAllocationLifetime.allocate_all_prefix heap cell hHeap B hB borrowed steps

theorem encodeAt_trace_work (cell : Cell) (depth : ℕ) :
    (encodeAt cell depth).1.2.length ≤ 2*(encodeAt cell depth).2.work := by
  cases cell with
  | leaf word =>
      have hF := BinaryHeapTapeMeasured.fieldAt_trace_work word.numerator (depth+1)
      have hS := BinaryHeapTapeMeasured.fieldAt_trace_work word.denominator (depth+1)
      have hJ := BinaryHeapTapeMeasured.appendAt_trace_work
        (BinaryHeapTapeMeasured.fieldAt word.numerator (depth+1)).1.1
        (BinaryHeapTapeMeasured.fieldAt word.denominator (depth+1)).1.1 (depth+1)
      simp only [encodeAt,List.length_cons,List.length_append]
      omega
  | branch left right =>
      have hF := BinaryHeapTapeMeasured.fieldAt_trace_work left (depth+1)
      have hS := BinaryHeapTapeMeasured.fieldAt_trace_work right (depth+1)
      have hJ := BinaryHeapTapeMeasured.appendAt_trace_work
        (BinaryHeapTapeMeasured.fieldAt left (depth+1)).1.1
        (BinaryHeapTapeMeasured.fieldAt right (depth+1)).1.1 (depth+1)
      simp only [encodeAt,List.length_cons,List.length_append]
      omega

theorem countAt_trace_work {α : Type*} (items : List α) (counter : Pointer) (depth : ℕ) :
    (countAt items counter depth).1.2.length ≤ 2*(countAt items counter depth).2.work := by
  induction items generalizing counter depth with
  | nil => simp [countAt]
  | cons item rest ih =>
      have hc := BinaryWordStoreMeasured.carryAt_trace_work counter (depth+1)
      have hl := ih (BinaryWordStoreMeasured.carryAt counter (depth+1)).1.1 (depth+1)
      simp only [countAt,List.length_cons,List.length_append]
      omega

theorem countAt_frames {α : Type*} (items : List α) (counter : Pointer) (depth : ℕ) :
    framePeak (countAt items counter depth).1.2 ≤ depth+(countAt items counter depth).2.work := by
  have h := (BinaryPRGHeapAllocationLifetime.countWithTrace_bound items counter).2
  have hu := framePeak_under depth (BinaryPRGHeapAllocationLifetime.countWithTrace items counter).2
  rw [countAt_erases,countAt_charge]
  dsimp only
  omega

theorem allocateAt_trace_work (heap : Heap) (cell : Cell) (depth : ℕ) :
    (allocateAt heap cell depth).1.2.length ≤ 2*(allocateAt heap cell depth).2.work := by
  have he := encodeAt_trace_work cell (depth+1)
  have hw := BinaryHeapTapeMeasured.appendAt_trace_work heap.tape (encodeAt cell (depth+1)).1.1 (depth+1)
  have hc := countAt_trace_work (encodeAt cell (depth+1)).1.1 heap.next (depth+1)
  simp only [allocateAt,List.length_cons,List.length_append]
  omega

theorem allocateAt_frames (heap : Heap) (cell : Cell) (depth : ℕ) :
    framePeak (allocateAt heap cell depth).1.2 ≤ depth+(allocateAt heap cell depth).2.work := by
  have h := (BinaryPRGHeapAllocationLifetime.allocateWithTrace_bound heap cell).2
  have hu := framePeak_under depth (BinaryPRGHeapAllocationLifetime.allocateWithTrace heap cell).2
  rw [allocateAt_erases,allocateAt_charge]
  dsimp only
  omega

end Blotto.BinaryHeapAllocationMeasured
