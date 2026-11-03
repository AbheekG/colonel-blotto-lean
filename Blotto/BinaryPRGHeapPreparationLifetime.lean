import Blotto.BinaryPRGHeapAllocationLifetime
import Blotto.BinaryPRGHeapResourceInputBounds

/-! Physical heap construction follows both recursive child builds and each
actual tape allocator. The trace retains all old tape/counter versions and
temporary source records; it does not construct a shadow logical tree. -/

namespace Blotto.BinaryPRGHeapPreparationLifetime
open BinaryRationalNormalization BinaryPRGWordStoreHeap BinarySeedPreparationSpace
open BinaryPRGHeapPrimitiveLifetime BinaryPRGHeapAllocationLifetime
set_option maxHeartbeats 1500000

def buildWithTrace (fallback : SignedWord) : List Bool → List SignedWord → Heap → Built × Trace
  | [],[],heap =>
      let produced := allocateWithTrace heap (.leaf fallback)
      (⟨produced.1.1,produced.1.2,[]⟩,[.frames 2,.arrayAllocation 16] ++ under 1 produced.2)
  | [],word :: rest,heap =>
      let produced := allocateWithTrace heap (.leaf word)
      (⟨produced.1.1,produced.1.2,rest⟩,[.frames 2,.arrayAllocation 16] ++ under 1 produced.2)
  | _ :: ruler,items,heap =>
      let first := buildWithTrace fallback ruler items heap
      let second := buildWithTrace fallback ruler first.1.remaining first.1.heap
      let produced := allocateWithTrace second.1.heap (.branch first.1.root second.1.root)
      (⟨produced.1.1,produced.1.2,second.1.remaining⟩,
        [.frames 2,.arrayAllocation 24] ++ under 1 first.2 ++ under 1 second.2 ++ under 1 produced.2)

theorem buildWithTrace_erasure (fallback : SignedWord) (ruler : List Bool) (items : List SignedWord) (heap : Heap) :
    (buildWithTrace fallback ruler items heap).1 =
      (BinaryPRGWordStoreHeapMachine.buildWithWork fallback ruler items heap).1 := by
  induction ruler generalizing items heap with
  | nil => cases items <;> simp only [buildWithTrace,BinaryPRGWordStoreHeapMachine.buildWithWork,allocateWithTrace_erasure]
  | cons bit ruler ih =>
      simp only [buildWithTrace,BinaryPRGWordStoreHeapMachine.buildWithWork,ih,allocateWithTrace_erasure]

theorem buildWithTrace_bound (fallback : SignedWord) (ruler : List Bool) (items : List SignedWord) (heap : Heap) :
    cells (buildWithTrace fallback ruler items heap).2 + 8 ≤
        price (BinaryPRGWordStoreHeapMachine.buildWithWork fallback ruler items heap).2 ∧
      framePeak (buildWithTrace fallback ruler items heap).2 ≤
        (BinaryPRGWordStoreHeapMachine.buildWithWork fallback ruler items heap).2.work + 8 := by
  induction ruler generalizing items heap with
  | nil =>
      cases items with
      | nil =>
          have h := allocateWithTrace_bound heap (.leaf fallback)
          have f := framePeak_under 1 (allocateWithTrace heap (.leaf fallback)).2
          simp only [buildWithTrace,BinaryPRGWordStoreHeapMachine.buildWithWork,
            BinaryPRGWordStoreHeapMachine.Charge.add,cells,listCells_append,arraySlots_append,
            listCells_under,arraySlots_under,listCells,arraySlots,framePeak_append,framePeak,price] at h ⊢
          exact ⟨by omega,by omega⟩
      | cons word rest =>
          have h := allocateWithTrace_bound heap (.leaf word)
          have f := framePeak_under 1 (allocateWithTrace heap (.leaf word)).2
          simp only [buildWithTrace,BinaryPRGWordStoreHeapMachine.buildWithWork,
            BinaryPRGWordStoreHeapMachine.Charge.add,cells,listCells_append,arraySlots_append,
            listCells_under,arraySlots_under,listCells,arraySlots,framePeak_append,framePeak,price] at h ⊢
          exact ⟨by omega,by omega⟩
  | cons bit ruler ih =>
      let first := (BinaryPRGWordStoreHeapMachine.buildWithWork fallback ruler items heap).1
      let second := (BinaryPRGWordStoreHeapMachine.buildWithWork fallback ruler first.remaining first.heap).1
      have hFirst := ih items heap
      have hSecond := ih first.remaining first.heap
      have hAlloc := allocateWithTrace_bound second.heap (.branch first.root second.root)
      have fFirst := framePeak_under 1 (buildWithTrace fallback ruler items heap).2
      have fSecond := framePeak_under 1 (buildWithTrace fallback ruler first.remaining first.heap).2
      have fAlloc := framePeak_under 1 (allocateWithTrace second.heap (.branch first.root second.root)).2
      simp only [buildWithTrace,BinaryPRGWordStoreHeapMachine.buildWithWork,buildWithTrace_erasure]
      change cells ([.frames 2,.arrayAllocation 24] ++ under 1 (buildWithTrace fallback ruler items heap).2 ++
          under 1 (buildWithTrace fallback ruler first.remaining first.heap).2 ++
          under 1 (allocateWithTrace second.heap (.branch first.root second.root)).2) + 8 ≤
          price ((BinaryPRGWordStoreHeapMachine.buildWithWork fallback ruler items heap).2.add
            ((BinaryPRGWordStoreHeapMachine.buildWithWork fallback ruler first.remaining first.heap).2.add
              ((BinaryPRGWordStoreHeapMachine.allocateWithWork second.heap (.branch first.root second.root)).2.add ⟨8,8⟩))) ∧ _
      simp only [BinaryPRGWordStoreHeapMachine.Charge.add,cells,listCells_append,arraySlots_append,
        listCells_under,arraySlots_under,listCells,arraySlots,framePeak_append,framePeak,price] at hFirst hSecond hAlloc ⊢
      dsimp only [first,second] at hFirst hSecond hAlloc fSecond fAlloc ⊢
      exact ⟨by omega,by omega⟩

def prepareWithTrace (fallback : SignedWord) (items : List SignedWord) : Store × Trace :=
  let counted := countWithTrace items []
  let built := buildWithTrace fallback counted.1 items empty
  (⟨counted.1,built.1.heap,built.1.root⟩,
    [.frames 2,.arrayAllocation 16] ++ under 1 counted.2 ++ under 1 built.2)

theorem prepareWithTrace_erasure (fallback : SignedWord) (items : List SignedWord) :
    (prepareWithTrace fallback items).1 = (BinaryPRGWordStoreHeapMachine.prepareWithWork fallback items).1 := by
  simp only [prepareWithTrace,BinaryPRGWordStoreHeapMachine.prepareWithWork,countWithTrace_erasure,buildWithTrace_erasure]

theorem prepareWithTrace_bound (fallback : SignedWord) (items : List SignedWord) :
    cells (prepareWithTrace fallback items).2 + 8 ≤ price (BinaryPRGWordStoreHeapMachine.prepareWithWork fallback items).2 ∧
      framePeak (prepareWithTrace fallback items).2 ≤ (BinaryPRGWordStoreHeapMachine.prepareWithWork fallback items).2.work + 9 := by
  have hCount := countWithTrace_bound items []
  have hBuild := buildWithTrace_bound fallback (BinaryPRGWordStoreHeapMachine.countWithWork items []).1 items empty
  have fCount := framePeak_under 1 (countWithTrace items []).2
  have fBuild := framePeak_under 1 (buildWithTrace fallback (BinaryPRGWordStoreHeapMachine.countWithWork items []).1 items empty).2
  simp only [prepareWithTrace,BinaryPRGWordStoreHeapMachine.prepareWithWork,countWithTrace_erasure,
    BinaryPRGWordStoreHeapMachine.Charge.add,cells,listCells_append,arraySlots_append,listCells_under,arraySlots_under,
    listCells,arraySlots,framePeak_append,framePeak,price] at hCount hBuild ⊢
  exact ⟨by omega,by omega⟩

theorem prepare_all_prefix (fallback : SignedWord) (items : List SignedWord) (borrowed steps : ℕ) :
    retainedHeap borrowed (prepareWithTrace fallback items).2 steps ≤
        borrowed + 32 * BinaryPRGWordStoreHeapMachine.preparationBound fallback items ∧
      framePeak ((prepareWithTrace fallback items).2.take steps) ≤
        BinaryPRGWordStoreHeapMachine.preparationBound fallback items + 9 := by
  have hTrace := prepareWithTrace_bound fallback items
  have hCharge := BinaryPRGWordStoreHeapMachine.prepareWithWork_bounds fallback items
  have hCells : listCells (prepareWithTrace fallback items).2 + arraySlots (prepareWithTrace fallback items).2 ≤
      32 * BinaryPRGWordStoreHeapMachine.preparationBound fallback items := by
    simp only [cells,price] at hTrace
    omega
  exact ⟨BinaryBooleanPrimitiveLifetime.prefix_heap _ _ borrowed steps hCells,
    (framePeak_take_le _ _).trans (hTrace.2.trans (Nat.add_le_add_right hCharge.1 9))⟩

theorem original_array_build_all_prefix {n : ℕ} (capacity input : FixedArrayTable n SignedWord)
    (W : ℕ) (hW : 1 ≤ W) (hInput : ∀ j,width (input.read j) ≤ W) (borrowed steps : ℕ) :
    let ruler := BinaryCarryCounter.count capacity.data.toList []
    let trace := (buildWithTrace BinaryRationalOpcode.zero ruler input.data.toList empty).2
    let B := (4 * n + 1) * (BinaryPRGWordStoreHeapMachine.allocationBound
      (BinaryPRGHeapResourceInputBounds.initialHeapBound n W) + 8)
    retainedHeap borrowed trace steps ≤ borrowed + 32 * B ∧
      framePeak (trace.take steps) ≤ B + 8 := by
  let ruler := BinaryCarryCounter.count capacity.data.toList []
  let K := BinaryPRGHeapResourceInputBounds.initialHeapBound n W
  let B := (4 * n + 1) * (BinaryPRGWordStoreHeapMachine.allocationBound K + 8)
  have hHeap := BinaryPRGHeapResourceInputBounds.prepared_heap_bound capacity input W hW hInput
  change (BinaryPRGWordStoreHeapMachine.buildWithWork BinaryRationalOpcode.zero ruler input.data.toList empty).1.heap.tape.length ≤ K at hHeap
  rw [BinaryPRGWordStoreHeapMachine.buildWithWork_erasure] at hHeap
  have hCharge := BinaryPRGWordStoreHeapMachine.buildWithWork_bounds BinaryRationalOpcode.zero
    ruler input.data.toList empty empty_valid K hHeap
  have hNodes := BinaryPRGHeapResourceInputBounds.source_nodes capacity
  change BinaryPRGWordStoreHeapMachine.nodes ruler.length ≤ 4 * n + 1 at hNodes
  have hWork := hCharge.1.trans (Nat.mul_le_mul_right
    (BinaryPRGWordStoreHeapMachine.allocationBound K + 8) hNodes)
  have hAlloc := hCharge.2.trans (Nat.mul_le_mul_right
    (BinaryPRGWordStoreHeapMachine.allocationBound K + 8) hNodes)
  have hTrace := buildWithTrace_bound BinaryRationalOpcode.zero ruler input.data.toList empty
  have hCells : listCells (buildWithTrace BinaryRationalOpcode.zero ruler input.data.toList empty).2 +
      arraySlots (buildWithTrace BinaryRationalOpcode.zero ruler input.data.toList empty).2 ≤ 32 * B := by
    simp only [cells,price] at hTrace
    dsimp only [B]
    omega
  have hPrefix := BinaryBooleanPrimitiveLifetime.prefix_heap
    (buildWithTrace BinaryRationalOpcode.zero ruler input.data.toList empty).2 (32 * B) borrowed steps hCells
  exact ⟨hPrefix,(framePeak_take_le _ _).trans (hTrace.2.trans (Nat.add_le_add_right hWork 8))⟩

end Blotto.BinaryPRGHeapPreparationLifetime
