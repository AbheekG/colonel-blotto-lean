import Blotto.BinaryPhysicalNumericalReadbackLifetime
import Blotto.BinaryPRGHeapInitialLifetime

/-! Certified persistent-tree builds from complete physical numerical-store
readback. The selected one-pass resource route consumes their returned heaps,
builder allowance, and retained source trace. -/
namespace Blotto.BinaryPhysicalHeapInputLifetime
open BinaryRationalNormalization BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryPRGPhysicalRawRequestLifetime
open BinaryPRGHeapStoredTree (Stored)
set_option autoImplicit false
set_option maxHeartbeats 300000

def RawArraysAt (capacity resource : List SignedWord) (ruler : List Bool) : Type :=
  Stored (BinaryPRGWordControllerWordStore.build BinaryRationalOpcode.zero ruler capacity).1 ×
    Stored (BinaryPRGWordControllerWordStore.build BinaryRationalOpcode.zero ruler resource).1

def rawArraysWithTrace (capacity resource : List SignedWord) :
    (Σ ruler : List Bool, RawArraysAt capacity resource ruler) × Trace :=
  let counted := BinaryPRGHeapAllocationLifetime.countWithTrace capacity []
  let limits := BinaryPRGHeapRulerLifetime.prepareRulerWithTrace
    BinaryRationalOpcode.zero counted.1 capacity
  let bids := BinaryPRGHeapRulerLifetime.prepareRulerWithTrace
    BinaryRationalOpcode.zero counted.1 resource
  (⟨counted.1,(limits.1,bids.1)⟩,
    wrapList (3*capacity.length) 64 (3*capacity.length+4)
      [counted.2,limits.2,bids.2])

/-- A work allowance read from the two heaps built by the selected traced
source. The old data and trace are reused, with no second tree build. -/
def rawArraysWithTraceAndBuildWork (capacity resource : List SignedWord) :
    ((Σ ruler : List Bool, RawArraysAt capacity resource ruler) × Trace) × ℕ :=
  let built := rawArraysWithTrace capacity resource
  let depth := built.1.1.length
  (built,
    BinaryPRGWordStoreHeapMachine.nodes depth *
      (BinaryPRGWordStoreHeapMachine.allocationBound
        built.1.2.1.heap.tape.length+8) +
    BinaryPRGWordStoreHeapMachine.nodes depth *
      (BinaryPRGWordStoreHeapMachine.allocationBound
        built.1.2.2.heap.tape.length+8))

theorem rawArraysWithTraceAndBuildWork_erases
    (capacity resource : List SignedWord) :
    (rawArraysWithTraceAndBuildWork capacity resource).1 =
      rawArraysWithTrace capacity resource := rfl

theorem rawArraysWithTraceAndBuildWork_covers_native
    (capacity resource : List SignedWord) :
    let ruler := (BinaryPRGHeapAllocationLifetime.countWithTrace capacity []).1
    (BinaryPRGHeapStoredTree.prepareRulerWithWork
      BinaryRationalOpcode.zero ruler capacity).2.work +
    (BinaryPRGHeapStoredTree.prepareRulerWithWork
      BinaryRationalOpcode.zero ruler resource).2.work ≤
      (rawArraysWithTraceAndBuildWork capacity resource).2 := by
  let ruler := (BinaryPRGHeapAllocationLifetime.countWithTrace capacity []).1
  have hl := BinaryPRGHeapStoredTree.prepareRulerWithWork_workBound
    BinaryRationalOpcode.zero ruler capacity
  have hr := BinaryPRGHeapStoredTree.prepareRulerWithWork_workBound
    BinaryRationalOpcode.zero ruler resource
  have hLimit := BinaryPRGHeapRulerLifetime.prepareRulerWithTrace_erasure
    BinaryRationalOpcode.zero ruler capacity
  have hBids := BinaryPRGHeapRulerLifetime.prepareRulerWithTrace_erasure
    BinaryRationalOpcode.zero ruler resource
  unfold rawArraysWithTraceAndBuildWork rawArraysWithTrace
  dsimp only
  change (BinaryPRGHeapStoredTree.prepareRulerWithWork
    BinaryRationalOpcode.zero ruler capacity).2.work +
    (BinaryPRGHeapStoredTree.prepareRulerWithWork
      BinaryRationalOpcode.zero ruler resource).2.work ≤
    BinaryPRGWordStoreHeapMachine.nodes ruler.length *
      (BinaryPRGWordStoreHeapMachine.allocationBound
        (BinaryPRGHeapRulerLifetime.prepareRulerWithTrace
          BinaryRationalOpcode.zero ruler capacity).1.heap.tape.length+8)+
    BinaryPRGWordStoreHeapMachine.nodes ruler.length *
      (BinaryPRGWordStoreHeapMachine.allocationBound
        (BinaryPRGHeapRulerLifetime.prepareRulerWithTrace
          BinaryRationalOpcode.zero ruler resource).1.heap.tape.length+8)
  rw [hLimit,hBids]
  omega

theorem rawArraysWithTraceAndBuildWork_covers_native_allocated
    (capacity resource : List SignedWord) :
    let ruler := (BinaryPRGHeapAllocationLifetime.countWithTrace capacity []).1
    (BinaryPRGHeapStoredTree.prepareRulerWithWork
      BinaryRationalOpcode.zero ruler capacity).2.allocatedBits +
    (BinaryPRGHeapStoredTree.prepareRulerWithWork
      BinaryRationalOpcode.zero ruler resource).2.allocatedBits ≤
      (rawArraysWithTraceAndBuildWork capacity resource).2 := by
  let ruler := (BinaryPRGHeapAllocationLifetime.countWithTrace capacity []).1
  have hl := BinaryPRGHeapStoredTree.prepareRulerWithWork_allocatedBound
    BinaryRationalOpcode.zero ruler capacity
  have hr := BinaryPRGHeapStoredTree.prepareRulerWithWork_allocatedBound
    BinaryRationalOpcode.zero ruler resource
  have hLimit := BinaryPRGHeapRulerLifetime.prepareRulerWithTrace_erasure
    BinaryRationalOpcode.zero ruler capacity
  have hBids := BinaryPRGHeapRulerLifetime.prepareRulerWithTrace_erasure
    BinaryRationalOpcode.zero ruler resource
  unfold rawArraysWithTraceAndBuildWork rawArraysWithTrace
  dsimp only
  change (BinaryPRGHeapStoredTree.prepareRulerWithWork
    BinaryRationalOpcode.zero ruler capacity).2.allocatedBits +
    (BinaryPRGHeapStoredTree.prepareRulerWithWork
      BinaryRationalOpcode.zero ruler resource).2.allocatedBits ≤
    BinaryPRGWordStoreHeapMachine.nodes ruler.length *
      (BinaryPRGWordStoreHeapMachine.allocationBound
        (BinaryPRGHeapRulerLifetime.prepareRulerWithTrace
          BinaryRationalOpcode.zero ruler capacity).1.heap.tape.length+8)+
    BinaryPRGWordStoreHeapMachine.nodes ruler.length *
      (BinaryPRGWordStoreHeapMachine.allocationBound
        (BinaryPRGHeapRulerLifetime.prepareRulerWithTrace
          BinaryRationalOpcode.zero ruler resource).1.heap.tape.length+8)
  rw [hLimit,hBids]
  omega

/-- The returned-heap allowance also bounds the retained source trace of the
two actual builds, up to the counter and the enclosing list/frame control. -/
theorem rawArraysWithTrace_usage (capacity resource : List SignedWord) :
    usage (rawArraysWithTrace capacity resource).2 ≤
      33 * (BinaryPRGWordStoreHeapMachine.countBound capacity.length 0 +
        (rawArraysWithTraceAndBuildWork capacity resource).2) +
      6 * capacity.length + 130 := by
  let counted := BinaryPRGHeapAllocationLifetime.countWithTrace capacity []
  let limits := BinaryPRGHeapRulerLifetime.prepareRulerWithTrace
    BinaryRationalOpcode.zero counted.1 capacity
  let bids := BinaryPRGHeapRulerLifetime.prepareRulerWithTrace
    BinaryRationalOpcode.zero counted.1 resource
  have hCount := BinaryPRGHeapRulerLifetime.count_usage capacity ([] : List Bool)
  have hLimitHeap :
      (BinaryPRGHeapStoredTree.prepareRulerWithWork
        BinaryRationalOpcode.zero counted.1 capacity).1.heap.tape.length ≤
        limits.1.heap.tape.length := by
    rw [BinaryPRGHeapRulerLifetime.prepareRulerWithTrace_erasure]
  have hBidHeap :
      (BinaryPRGHeapStoredTree.prepareRulerWithWork
        BinaryRationalOpcode.zero counted.1 resource).1.heap.tape.length ≤
        bids.1.heap.tape.length := by
    rw [BinaryPRGHeapRulerLifetime.prepareRulerWithTrace_erasure]
  have hLimit := BinaryPRGHeapRulerLifetime.prepareRulerWithTrace_usage
    BinaryRationalOpcode.zero counted.1 capacity limits.1.heap.tape.length hLimitHeap
  have hBid := BinaryPRGHeapRulerLifetime.prepareRulerWithTrace_usage
    BinaryRationalOpcode.zero counted.1 resource bids.1.heap.tape.length hBidHeap
  change usage counted.2 ≤
    33 * BinaryPRGWordStoreHeapMachine.countBound capacity.length 0 at hCount
  change usage limits.2 ≤
    33 * (BinaryPRGWordStoreHeapMachine.nodes counted.1.length *
      (BinaryPRGWordStoreHeapMachine.allocationBound limits.1.heap.tape.length + 8)) + 28 at hLimit
  change usage bids.2 ≤
    33 * (BinaryPRGWordStoreHeapMachine.nodes counted.1.length *
      (BinaryPRGWordStoreHeapMachine.allocationBound bids.1.heap.tape.length + 8)) + 28 at hBid
  have hWrap := wrapList_usage (3*capacity.length) 64 (3*capacity.length+4)
    [counted.2,limits.2,bids.2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hWrap
  unfold rawArraysWithTraceAndBuildWork rawArraysWithTrace
  dsimp only
  change usage (wrapList (3*capacity.length) 64 (3*capacity.length+4)
    [counted.2,limits.2,bids.2]) ≤
    33 * (BinaryPRGWordStoreHeapMachine.countBound capacity.length 0 +
      (BinaryPRGWordStoreHeapMachine.nodes counted.1.length *
        (BinaryPRGWordStoreHeapMachine.allocationBound limits.1.heap.tape.length+8) +
      BinaryPRGWordStoreHeapMachine.nodes counted.1.length *
        (BinaryPRGWordStoreHeapMachine.allocationBound bids.1.heap.tape.length+8))) +
    6*capacity.length+130
  omega

theorem rawArraysWithTrace_all_prefix (capacity resource : List SignedWord)
    (borrowed steps : ℕ) :
    let B := 33 * (BinaryPRGWordStoreHeapMachine.countBound capacity.length 0 +
      (rawArraysWithTraceAndBuildWork capacity resource).2) +
      6 * capacity.length + 130
    retainedHeap borrowed (rawArraysWithTrace capacity resource).2 steps ≤
        borrowed + B ∧
      framePeak ((rawArraysWithTrace capacity resource).2.take steps) ≤ B :=
  all_prefix _ _ (rawArraysWithTrace_usage capacity resource) borrowed steps

theorem rawArraysWithTraceAndBuildWork_input_bound {n : ℕ}
    (capacity resource : FixedArrayTable n SignedWord) (W : ℕ)
    (hW : 1 ≤ W)
    (hCapacity : ∀ j,width (capacity.read j) ≤ W)
    (hResource : ∀ j,width (resource.read j) ≤ W) :
    (rawArraysWithTraceAndBuildWork capacity.data.toList
      resource.data.toList).2 ≤
      2*(4*n+1)*
        (BinaryPRGWordStoreHeapMachine.allocationBound
          (BinaryPRGHeapResourceInputBounds.initialHeapBound n W)+8) := by
  let ruler := (BinaryPRGHeapAllocationLifetime.countWithTrace
    capacity.data.toList []).1
  let K := BinaryPRGHeapResourceInputBounds.initialHeapBound n W
  have hRuler : ruler = BinaryCarryCounter.count capacity.data.toList [] :=
    (BinaryPRGHeapAllocationLifetime.countWithTrace_erasure
      capacity.data.toList []).trans
      (BinaryPRGWordStoreHeapMachine.countWithWork_erasure
        capacity.data.toList [])
  have hNodes : BinaryPRGWordStoreHeapMachine.nodes ruler.length ≤ 4*n+1 := by
    rw [hRuler]
    exact BinaryPRGHeapResourceInputBounds.source_nodes capacity
  have hCap :
      (BinaryPRGHeapRulerLifetime.prepareRulerWithTrace
        BinaryRationalOpcode.zero ruler capacity.data.toList).1.heap.tape.length ≤ K := by
    rw [BinaryPRGHeapRulerLifetime.prepareRulerWithTrace_erasure,hRuler]
    exact BinaryPRGHeapResourceInputBounds.prepared_heap_bound
      capacity capacity W hW hCapacity
  have hRes :
      (BinaryPRGHeapRulerLifetime.prepareRulerWithTrace
        BinaryRationalOpcode.zero ruler resource.data.toList).1.heap.tape.length ≤ K := by
    rw [BinaryPRGHeapRulerLifetime.prepareRulerWithTrace_erasure,hRuler]
    exact BinaryPRGHeapResourceInputBounds.prepared_heap_bound
      capacity resource W hW hResource
  have hAC : BinaryPRGWordStoreHeapMachine.allocationBound
      (BinaryPRGHeapRulerLifetime.prepareRulerWithTrace
        BinaryRationalOpcode.zero ruler capacity.data.toList).1.heap.tape.length ≤
      BinaryPRGWordStoreHeapMachine.allocationBound K := by
    unfold BinaryPRGWordStoreHeapMachine.allocationBound
    gcongr
  have hAR : BinaryPRGWordStoreHeapMachine.allocationBound
      (BinaryPRGHeapRulerLifetime.prepareRulerWithTrace
        BinaryRationalOpcode.zero ruler resource.data.toList).1.heap.tape.length ≤
      BinaryPRGWordStoreHeapMachine.allocationBound K := by
    unfold BinaryPRGWordStoreHeapMachine.allocationBound
    gcongr
  have hC := Nat.mul_le_mul hNodes (Nat.add_le_add_right hAC 8)
  have hR := Nat.mul_le_mul hNodes (Nat.add_le_add_right hAR 8)
  unfold rawArraysWithTraceAndBuildWork rawArraysWithTrace
  dsimp only
  change BinaryPRGWordStoreHeapMachine.nodes ruler.length *
      (BinaryPRGWordStoreHeapMachine.allocationBound
        (BinaryPRGHeapRulerLifetime.prepareRulerWithTrace
          BinaryRationalOpcode.zero ruler capacity.data.toList).1.heap.tape.length+8)+
    BinaryPRGWordStoreHeapMachine.nodes ruler.length *
      (BinaryPRGWordStoreHeapMachine.allocationBound
        (BinaryPRGHeapRulerLifetime.prepareRulerWithTrace
          BinaryRationalOpcode.zero ruler resource.data.toList).1.heap.tape.length+8) ≤ _
  calc
    _ ≤ (4*n+1)*(BinaryPRGWordStoreHeapMachine.allocationBound K+8)+
        (4*n+1)*(BinaryPRGWordStoreHeapMachine.allocationBound K+8) :=
      Nat.add_le_add hC hR
    _ = 2*(4*n+1)*
        (BinaryPRGWordStoreHeapMachine.allocationBound K+8) := by ring

theorem rawArrays_trace {n : ℕ}
    (capacity resource : FixedArrayTable n SignedWord) :
    (rawArraysWithTrace capacity.data.toList resource.data.toList).2 =
      (BinaryPRGHeapInitialLifetime.arraysWithTrace capacity resource).2 := by
  unfold rawArraysWithTrace BinaryPRGHeapInitialLifetime.arraysWithTrace
  simp only [Array.length_toList,capacity.size]

theorem rawArrays_value {n : ℕ}
    (capacity resource : FixedArrayTable n SignedWord) :
    let arrays := rawArraysWithTrace capacity.data.toList resource.data.toList
    ∃ hRuler : arrays.1.1 = BinaryCarryCounter.count capacity.data.toList [],
      (hRuler ▸ arrays.1.2 :
        BinaryPRGHeapInitialLifetime.ArraysAt capacity resource
          (BinaryCarryCounter.count capacity.data.toList [])) =
        (BinaryPRGHeapInitialLifetime.arraysWithTrace capacity resource).1 := by
  have hRuler :
      (rawArraysWithTrace capacity.data.toList resource.data.toList).1.1 =
        BinaryCarryCounter.count capacity.data.toList [] :=
    (BinaryPRGHeapAllocationLifetime.countWithTrace_erasure capacity.data.toList []).trans
      (BinaryPRGWordStoreHeapMachine.countWithWork_erasure capacity.data.toList [])
  refine ⟨hRuler,?_⟩
  unfold rawArraysWithTrace BinaryPRGHeapInitialLifetime.arraysWithTrace
  rfl

abbrev ReadbackTrees : Type :=
  Σ capacity : List SignedWord, Σ resource : List SignedWord,
    Σ ruler : List Bool, RawArraysAt capacity resource ruler

def readbackBuildWithTrace {n : ℕ} (request : Request n) (rich : Bool) :
    Option ReadbackTrees × Trace :=
  let readback := BinaryPhysicalNumericalReadbackLifetime.readPairWithTrace request
  match readback.1 with
  | none => (none,wrap 16 2 [readback.2])
  | some (capacity,poor) =>
      let resource := if rich then capacity else poor
      let arrays := rawArraysWithTrace capacity resource
      (some ⟨capacity,resource,arrays.1⟩,
        wrap 32 2 [readback.2,arrays.2])

theorem accepted_readbackBuild_words (frame : List Bool)
    (parsed : (Σ n,Request n) × List Bool)
    (hParsed : (readWithTrace frame).1 = some parsed)
    (rich : Bool) :
    (readbackBuildWithTrace parsed.1.2 rich).1.map
      (fun trees => (trees.1,trees.2.1)) =
        some (parsed.1.2.logical.request.prepared.lengths.data.toList,
          if rich then parsed.1.2.logical.request.prepared.lengths.data.toList
            else parsed.1.2.logical.request.prepared.poorResources.data.toList) := by
  unfold readbackBuildWithTrace
  dsimp only
  rw [BinaryPhysicalNumericalReadbackLifetime.accepted_pair_words frame parsed hParsed]
  rfl

theorem accepted_readbackBuild_success (frame : List Bool)
    (parsed : (Σ n,Request n) × List Bool)
    (hParsed : (readWithTrace frame).1 = some parsed)
    (rich : Bool) :
    ∃ trees, (readbackBuildWithTrace parsed.1.2 rich).1 = some trees := by
  have h := accepted_readbackBuild_words frame parsed hParsed rich
  cases hBuild : (readbackBuildWithTrace parsed.1.2 rich).1 with
  | none => simp only [hBuild,Option.map_none] at h; cases h
  | some trees => exact ⟨trees,rfl⟩

end Blotto.BinaryPhysicalHeapInputLifetime
