import Blotto.BinaryHeapConstructionPlan

/-! Actual counter and heap-construction allocated-bit charges are bounded by
their returned source work. This concerns the named Boolean charge model;
native headers, ownership and allocator/GC interpretation remain separate. -/
namespace Blotto.BinaryHeapConstructionChargeOrder
open BinaryRationalNormalization BinaryPRGWordStoreHeap
open BinaryPRGWordStoreHeapMachine
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem field (bits : List Bool) :
    (fieldWithWork bits).2.allocatedBits ≤ (fieldWithWork bits).2.work := by
  have h := fieldWithWork_price bits
  omega

theorem append (first second : List Bool) :
    (appendWithWork first second).2.allocatedBits ≤ (appendWithWork first second).2.work := by
  have h := appendWithWork_price first second
  omega

theorem encode (cell : Cell) :
    (encodeWithWork cell).2.allocatedBits ≤ (encodeWithWork cell).2.work := by
  cases cell with
  | leaf word =>
    have hf := field word.numerator
    have hs := field word.denominator
    have ha := append (fieldWithWork word.numerator).1 (fieldWithWork word.denominator).1
    simp only [encodeWithWork]
    omega
  | branch left right =>
    have hf := field left
    have hs := field right
    have ha := append (fieldWithWork left).1 (fieldWithWork right).1
    simp only [encodeWithWork]
    omega

theorem count {α : Type*} (items : List α) (counter : Pointer) :
    (countWithWork items counter).2.allocatedBits ≤ (countWithWork items counter).2.work := by
  induction items generalizing counter with
  | nil => simp [countWithWork]
  | cons item rest ih =>
    have h := ih (BinaryCarryCounter.increment counter)
    have hc := BinaryWordStoreLifetime.carry_length counter
    simp only [countWithWork]
    omega

theorem allocate (heap : Heap) (cell : Cell) :
    (allocateWithWork heap cell).2.allocatedBits ≤ (allocateWithWork heap cell).2.work := by
  have he := encode cell
  have ha := append heap.tape (encodeWithWork cell).1
  have hc := count (encodeWithWork cell).1 heap.next
  simp only [allocateWithWork]
  omega

theorem build (fallback : SignedWord) (ruler : List Bool) (items : List SignedWord) (heap : Heap) :
    (buildWithWork fallback ruler items heap).2.allocatedBits ≤
      (buildWithWork fallback ruler items heap).2.work := by
  induction ruler generalizing items heap with
  | nil =>
    cases items with
    | nil =>
      have h := allocate heap (.leaf fallback)
      simp only [buildWithWork,Charge.add]
      omega
    | cons word rest =>
      have h := allocate heap (.leaf word)
      simp only [buildWithWork,Charge.add]
      omega
  | cons bit ruler ih =>
    have hf := ih items heap
    have hs := ih (buildWithWork fallback ruler items heap).1.remaining
      (buildWithWork fallback ruler items heap).1.heap
    have ha := allocate
      (buildWithWork fallback ruler (buildWithWork fallback ruler items heap).1.remaining
        (buildWithWork fallback ruler items heap).1.heap).1.heap
      (.branch (buildWithWork fallback ruler items heap).1.root
        (buildWithWork fallback ruler (buildWithWork fallback ruler items heap).1.remaining
          (buildWithWork fallback ruler items heap).1.heap).1.root)
    simp only [buildWithWork,Charge.add]
    omega

theorem prepared (fallback : SignedWord) (ruler : List Bool) (items : List SignedWord) :
    (BinaryHeapConstructionPlan.prepareWithEmission fallback ruler items).1.2.allocatedBits ≤
      (BinaryHeapConstructionPlan.prepareWithEmission fallback ruler items).1.2.work := by
  rw [BinaryHeapConstructionPlan.prepare_compat]
  exact build fallback ruler items empty

theorem counted {α : Type*} (items : List α) (counter : Pointer) :
    (BinaryHeapConstructionPlan.countWithEmission items counter).1.2.allocatedBits ≤
      (BinaryHeapConstructionPlan.countWithEmission items counter).1.2.work := by
  rw [BinaryHeapConstructionPlan.count_compat]
  exact count items counter

end Blotto.BinaryHeapConstructionChargeOrder
