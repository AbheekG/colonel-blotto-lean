import Blotto.BinaryHeapAllocationMeasured
import Blotto.BinaryNumericalReadbackPlan

/-! Actual field/append/carry producers feed an allocator plan. All preceding
At records, including work and allocated-bit charges, are exact. No allocator
plan emits here. Primitive leaf traces and native metadata remain separate. -/
namespace Blotto.BinaryHeapAllocatorPlan
open BinaryRationalNormalization BinarySeedPreparationSpace BinaryPRGHeapTraceUsage BinaryTraceDepth BinaryTracePlanMeasured
open BinaryPRGWordStoreHeap
open BinaryPRGWordStoreHeapMachine (Charge)
open BinaryNumericalReadbackPlan (view offset)
open BinaryCachePrefixPlan (Bounded block_bound)
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem data_eq {α β : Type*} {record : (α × Plan) × β} {old : (α × Trace) × β}
    (h : view record = old) : record.1.1 = old.1.1 := congrArg (fun out => out.1.1) h

theorem trace_eq {α β : Type*} {record : (α × Plan) × β} {old : (α × Trace) × β}
    (h : view record = old) : denote record.1.2 = old.1.2 := congrArg (fun out => out.1.2) h

theorem charge_eq {α β : Type*} {record : (α × Plan) × β} {old : (α × Trace) × β}
    (h : view record = old) : record.2 = old.2 := congrArg Prod.snd h

def encodeAt : Cell → ℕ → (List Bool × Plan) × Charge
  | .leaf word,depth =>
      let first := BinaryHeapTapeMeasured.fieldAt word.numerator (depth+1)
      let second := BinaryHeapTapeMeasured.fieldAt word.denominator (depth+1)
      let joined := BinaryHeapTapeMeasured.appendAt first.1.1 second.1.1 (depth+1)
      ((false::word.negative::joined.1.1,.join (.block [.frames (depth+2),.arrayAllocation 8,.listAllocation 2])
        (.join (.block first.1.2) (.join (.block second.1.2) (.block joined.1.2)))),
        ⟨first.2.work+second.2.work+joined.2.work+4,first.2.allocatedBits+second.2.allocatedBits+joined.2.allocatedBits+2⟩)
  | .branch left right,depth =>
      let first := BinaryHeapTapeMeasured.fieldAt left (depth+1)
      let second := BinaryHeapTapeMeasured.fieldAt right (depth+1)
      let joined := BinaryHeapTapeMeasured.appendAt first.1.1 second.1.1 (depth+1)
      ((true::joined.1.1,.join (.block [.frames (depth+2),.arrayAllocation 8,.listAllocation 1])
        (.join (.block first.1.2) (.join (.block second.1.2) (.block joined.1.2)))),
        ⟨first.2.work+second.2.work+joined.2.work+3,first.2.allocatedBits+second.2.allocatedBits+joined.2.allocatedBits+1⟩)

theorem encode_refines (cell : Cell) (depth : ℕ) :
    view (encodeAt cell depth) = BinaryHeapAllocationMeasured.encodeAt cell depth := by
  cases cell <;> simp only [encodeAt,BinaryHeapAllocationMeasured.encodeAt,view,denote] <;> rfl

theorem encode_data (cell : Cell) (depth : ℕ) :
    (encodeAt cell depth).1.1 = (BinaryHeapAllocationMeasured.encodeAt cell depth).1.1 := data_eq (encode_refines cell depth)

theorem encode_trace (cell : Cell) (depth : ℕ) :
    denote (encodeAt cell depth).1.2 = (BinaryHeapAllocationMeasured.encodeAt cell depth).1.2 := trace_eq (encode_refines cell depth)

theorem encode_charge (cell : Cell) (depth : ℕ) :
    (encodeAt cell depth).2 = (BinaryHeapAllocationMeasured.encodeAt cell depth).2 := charge_eq (encode_refines cell depth)

theorem encode_bound (cell : Cell) (depth : ℕ) : Bounded (encodeAt cell depth).1.2 := by
  cases cell <;> simp only [Bounded,encodeAt,nodes,payload,List.length_cons,List.length_nil] <;> omega

def countAt {α : Type*} : List α → Pointer → ℕ → (Pointer × Plan) × Charge
  | [],counter,depth => ((counter,.block [.frames (depth+1),.arrayAllocation 8]),⟨1,0⟩)
  | _::rest,counter,depth =>
      let advanced := BinaryWordStoreMeasured.carryAt counter (depth+1)
      let later := countAt rest advanced.1.1 (depth+1)
      ((later.1.1,.join (.block [.frames (depth+2),.arrayAllocation 8]) (.join (.block advanced.1.2) later.1.2)),
        ⟨advanced.2+4*(counter.length+1)+later.2.work+4,advanced.1.1.length+later.2.allocatedBits⟩)

theorem count_refines {α : Type*} (items : List α) (counter : Pointer) (depth : ℕ) :
    view (countAt items counter depth) = BinaryHeapAllocationMeasured.countAt items counter depth := by
  induction items generalizing counter depth with
  | nil => rfl
  | cons item rest ih =>
      have h := ih (BinaryWordStoreMeasured.carryAt counter (depth+1)).1.1 (depth+1)
      simp only [countAt,BinaryHeapAllocationMeasured.countAt,view,denote,data_eq h,trace_eq h,charge_eq h]
      rfl

theorem count_data {α : Type*} (items : List α) (counter : Pointer) (depth : ℕ) :
    (countAt items counter depth).1.1 = (BinaryHeapAllocationMeasured.countAt items counter depth).1.1 := data_eq (count_refines items counter depth)

theorem count_trace {α : Type*} (items : List α) (counter : Pointer) (depth : ℕ) :
    denote (countAt items counter depth).1.2 = (BinaryHeapAllocationMeasured.countAt items counter depth).1.2 := trace_eq (count_refines items counter depth)

theorem count_charge {α : Type*} (items : List α) (counter : Pointer) (depth : ℕ) :
    (countAt items counter depth).2 = (BinaryHeapAllocationMeasured.countAt items counter depth).2 := charge_eq (count_refines items counter depth)

theorem count_bound {α : Type*} (items : List α) (counter : Pointer) (depth : ℕ) : Bounded (countAt items counter depth).1.2 := by
  induction items generalizing counter depth with
  | nil => exact block_bound _
  | cons item rest ih =>
      have h := ih (BinaryWordStoreMeasured.carryAt counter (depth+1)).1.1 (depth+1)
      simp only [Bounded,countAt,nodes,payload,List.length_cons,List.length_nil] at h ⊢
      omega

def allocateAt (heap : Heap) (cell : Cell) (depth : ℕ) : ((Pointer × Heap) × Plan) × Charge :=
  let encoded := encodeAt cell (depth+1)
  let written := BinaryHeapTapeMeasured.appendAt heap.tape encoded.1.1 (depth+1)
  let advanced := countAt encoded.1.1 heap.next (depth+1)
  (((heap.next,⟨written.1.1,advanced.1.1⟩),.join (.block [.frames (depth+2),.arrayAllocation 16])
    (.join encoded.1.2 (.join (.block written.1.2) advanced.1.2))),
    ⟨encoded.2.work+written.2.work+advanced.2.work+4*(heap.next.length+1)+6,
      encoded.2.allocatedBits+written.2.allocatedBits+advanced.2.allocatedBits+heap.next.length+4⟩)

theorem allocate_refines (heap : Heap) (cell : Cell) (depth : ℕ) :
    view (allocateAt heap cell depth) = BinaryHeapAllocationMeasured.allocateAt heap cell depth := by
  simp only [allocateAt,BinaryHeapAllocationMeasured.allocateAt,view,denote,
    encode_data,encode_trace,encode_charge,count_data,count_trace,count_charge]
  rfl

theorem allocate_data (heap : Heap) (cell : Cell) (depth : ℕ) :
    (allocateAt heap cell depth).1.1 = (BinaryPRGWordStoreHeapMachine.allocateWithWork heap cell).1 := by
  rw [data_eq (allocate_refines heap cell depth),BinaryHeapAllocationMeasured.allocateAt_erases,
    BinaryPRGHeapAllocationLifetime.allocateWithTrace_erasure]

theorem allocate_trace (heap : Heap) (cell : Cell) (depth : ℕ) :
    denote (allocateAt heap cell depth).1.2 = under depth (BinaryPRGHeapAllocationLifetime.allocateWithTrace heap cell).2 := by
  rw [trace_eq (allocate_refines heap cell depth),BinaryHeapAllocationMeasured.allocateAt_erases]

theorem allocate_charge (heap : Heap) (cell : Cell) (depth : ℕ) :
    (allocateAt heap cell depth).2 = (BinaryPRGWordStoreHeapMachine.allocateWithWork heap cell).2 := by
  rw [charge_eq (allocate_refines heap cell depth),BinaryHeapAllocationMeasured.allocateAt_charge]

theorem allocate_bound (heap : Heap) (cell : Cell) (depth : ℕ) : Bounded (allocateAt heap cell depth).1.2 := by
  have he := encode_bound cell (depth+1)
  have hc := count_bound (encodeAt cell (depth+1)).1.1 heap.next (depth+1)
  simp only [Bounded,allocateAt,nodes,payload,List.length_cons,List.length_nil] at he hc ⊢
  omega

end Blotto.BinaryHeapAllocatorPlan
