import Blotto.BinaryPRGHeapPreparationLifetime
import Blotto.BinaryPRGHeapTraceUsage

/-! One traced Boolean capacity ruler feeds both physical heap builds. The
logical build remains an erased type index, with no shadow tree at runtime. -/

namespace Blotto.BinaryPRGHeapRulerLifetime
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGWordStoreHeap
open BinaryPRGHeapTraceUsage
open BinaryPRGHeapStoredTree (Stored)
set_option maxHeartbeats 1500000

def prepareRulerWithTrace (fallback : SignedWord) (ruler : List Bool) (items : List SignedWord) :
    Stored (BinaryPRGWordControllerWordStore.build fallback ruler items).1 × Trace :=
  let built := BinaryPRGHeapPreparationLifetime.buildWithTrace fallback ruler items empty
  (⟨ruler,rfl,built.1.heap,built.1.root,
    (by rw [BinaryPRGHeapPreparationLifetime.buildWithTrace_erasure,BinaryPRGWordStoreHeapMachine.buildWithWork_erasure]
        exact (build_contract fallback ruler items empty empty_valid).1),
    (by rw [BinaryPRGHeapPreparationLifetime.buildWithTrace_erasure,BinaryPRGWordStoreHeapMachine.buildWithWork_erasure]
        exact (build_contract fallback ruler items empty empty_valid).2.2.1)⟩,
    wrap 16 2 [built.2])

theorem prepareRulerWithTrace_erasure (fallback : SignedWord) (ruler : List Bool) (items : List SignedWord) :
    (prepareRulerWithTrace fallback ruler items).1 =
      (BinaryPRGHeapStoredTree.prepareRulerWithWork fallback ruler items).1 := by
  simp only [prepareRulerWithTrace,BinaryPRGHeapStoredTree.prepareRulerWithWork,
    BinaryPRGHeapPreparationLifetime.buildWithTrace_erasure]

theorem prepareRulerWithTrace_usage (fallback : SignedWord) (ruler : List Bool) (items : List SignedWord)
    (K : ℕ) (hK : (BinaryPRGHeapStoredTree.prepareRulerWithWork fallback ruler items).1.heap.tape.length ≤ K) :
    usage (prepareRulerWithTrace fallback ruler items).2 ≤
      33 * (BinaryPRGWordStoreHeapMachine.nodes ruler.length *
        (BinaryPRGWordStoreHeapMachine.allocationBound K + 8)) + 28 := by
  have hHeap : (build fallback ruler items empty).heap.tape.length ≤ K := by
    simpa only [BinaryPRGHeapStoredTree.prepareRulerWithWork,BinaryPRGWordStoreHeapMachine.buildWithWork_erasure] using hK
  have hCharge := BinaryPRGWordStoreHeapMachine.buildWithWork_bounds fallback ruler items empty empty_valid K hHeap
  have hTrace := BinaryPRGHeapPreparationLifetime.buildWithTrace_bound fallback ruler items empty
  have hw := wrap_usage 16 2 [(BinaryPRGHeapPreparationLifetime.buildWithTrace fallback ruler items empty).2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  unfold prepareRulerWithTrace
  dsimp only
  unfold usage BinaryPRGHeapPrimitiveLifetime.cells BinaryPRGHeapPrimitiveLifetime.price at *
  omega

theorem count_usage {α : Type*} (items : List α) (counter : List Bool) :
    usage (BinaryPRGHeapAllocationLifetime.countWithTrace items counter).2 ≤
      33 * BinaryPRGWordStoreHeapMachine.countBound items.length counter.length := by
  have hTrace := BinaryPRGHeapAllocationLifetime.countWithTrace_bound items counter
  have hCharge := BinaryPRGWordStoreHeapMachine.countWithWork_bounds items counter
  have hAlloc : (BinaryPRGWordStoreHeapMachine.countWithWork items counter).2.allocatedBits ≤
      BinaryPRGWordStoreHeapMachine.countBound items.length counter.length := by
    apply hCharge.2.trans
    unfold BinaryPRGWordStoreHeapMachine.countBound
    nlinarith
  unfold usage BinaryPRGHeapPrimitiveLifetime.cells BinaryPRGHeapPrimitiveLifetime.price at *
  omega

end Blotto.BinaryPRGHeapRulerLifetime
