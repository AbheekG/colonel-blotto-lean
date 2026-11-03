import Blotto.BinaryPRGHeapNativeLifetimeBound
import Blotto.BinaryPRGHeapResourceThreeSource

/-! The reflected physical three-coordinate source closes complete retained
allocation from original height promises, without a lattice substitution. -/

namespace Blotto.BinaryPRGHeapThreeNativeLifetimeBound
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGHeapTraceUsage BinaryPRGHeapNativeLifetime
open BinaryPRGHeapResourceSource (capStore count)
open BinaryPRGHeapResourceLoop (Finished)
open BinaryPRGHeapResourceThreeSource (inputWidth initialCells pointerWidth heapCap)
open BinaryPRGHeapResourceThreeReservation (Reserved)
set_option maxHeartbeats 1500000

theorem returned_heap (s : ℕ) (hs : 2 ≤ s) (seed : BinarySeedLookupTree.Store)
    (capacity resource : FixedArrayTable 3 SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j))
    (hCapacity : ∀ j,RationalHeight (value (capacity.read j)) s)
    (hResource : ∀ j,RationalHeight (value (resource.read j)) s)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value)
    (result : Finished (capStore capacity) 3 (count capacity))
    (hSome : (sourceWithTrace seed capacity resource hC hR pc hp).1.2.1 = some result) :
    result.heap.tape.length ≤ heapCap s := by
  let prepared := BinaryPRGHeapResourceSource.initialWithWork capacity resource hC hR
  let cap := BinaryPRGHeapResourceSource.capStore capacity
  let W := inputWidth s
  let K := initialCells s
  let P := pointerWidth s
  let H := heapCap s
  have hHeight := expressionHeightBudget_ge_input s (3 * 2)
  have hW : 1 ≤ W := by unfold W inputWidth BinaryPRGWordControllerBooleanResourceThreeWork.widthBound; omega
  have hcWidth : ∀ j,width (capacity.read j) ≤ W := by
    intro j
    have hw := (hC j).2.trans (rationalWordWidth_of_height (hCapacity j))
    unfold W inputWidth BinaryPRGWordControllerBooleanResourceThreeWork.widthBound BinaryThreeResourceHeight.resourceHeight
    omega
  have hrWidth : ∀ j,width (resource.read j) ≤ W := by
    intro j
    have hw := (hR j).2.trans (rationalWordWidth_of_height (hResource j))
    unfold W inputWidth BinaryPRGWordControllerBooleanResourceThreeWork.widthBound BinaryThreeResourceHeight.resourceHeight
    omega
  have hHeaps := BinaryPRGHeapResourceInputBounds.initial_heaps_bound
    capacity resource hC hR W hW hcWidth hrWidth
  change prepared.1.1.heap.tape.length ≤ K ∧ prepared.1.2.heap.tape.length ≤ K at hHeaps
  have hd := BinaryPRGHeapResourceInputBounds.source_depth capacity
  change cap.width ≤ binaryWordWidth 3 at hd
  have hCap : ∀ j,RationalHeight (value ((BinaryPRGWordControllerBooleanResourceUpdate.table
      cap.cap cap.tree 3 (BinaryPRGHeapResourceSource.count capacity)).read j)) s := by
    rw [BinaryPRGWordControllerBooleanResourceSource.capacityTable]
    exact hCapacity
  have hState : BinaryPRGHeapResourceThreeStep.HeightInv 2 s prepared.1.2 := by
    unfold BinaryPRGHeapResourceThreeStep.HeightInv
    rw [BinaryPRGHeapResourceSource.initialWithWork_reference]
    exact BinaryPRGWordControllerBooleanResourceThreeWork.source_initial_height
      capacity resource hC hR s hResource
  have hGrowth : BinaryPRGHeapResourceUpdateBudget.growth cap.width W P ≤
      BinaryPRGHeapResourceUpdateBudget.growth (binaryWordWidth 3) W P := by
    unfold BinaryPRGHeapResourceUpdateBudget.growth
    gcongr
  have hReserved : Reserved 2 s P H prepared.1.2 := by
    refine ⟨hState,?_⟩
    have hm := Nat.mul_le_mul prepared.1.2.active_length_le hGrowth
    exact (Nat.add_le_add hHeaps.2 hm).trans
      (BinaryPRGHeapResourceReservation.source_room K 3 (binaryWordWidth 3) W)
  have hP : 0 < P := by unfold P pointerWidth BinaryPRGHeapResourceReservation.sourcePointerWidth; omega
  have hRoom : H < 2^P := BinaryPRGWordStoreHeap.quadratic_lt_capacity _
  have hBudget := BinaryPRGHeapResourceThreeReservation.reachableStepBudget
    (hC := BinaryPRGWordControllerBooleanResourceSource.capacityCanonical capacity hC)
    2 s hs hCap seed prepared.1.1 K H P hHeaps.1 hP hRoom
  rw [sourceWithTrace_erasure] at hSome
  change (BinaryPRGHeapResourceLoop.runWithWork seed prepared.1.1
    (BinaryPRGWordControllerBooleanResourceSource.capacityCanonical capacity hC) prepared.1.2 pc hp).1.1 = some result at hSome
  have hReturned := BinaryPRGHeapResourceLoopBudget.runWithWork_invariant seed prepared.1.1
    (BinaryPRGWordControllerBooleanResourceSource.capacityCanonical capacity hC)
    (Reserved 2 s P H) _ hBudget prepared.1.2 hReserved pc hp result hSome
  have h := hReturned.2
  change result.heap.tape.length ≤ H
  omega

def envelope (s indexWidth seedCap : ℕ) : ℕ :=
  BinaryPRGHeapInitialLifetimeBound.envelope 3 (inputWidth s) (binaryWordWidth 3) +
    BinaryPRGHeapLifetimePolynomial.threeLoopEnvelope s indexWidth seedCap +
    BinaryPRGHeapMaterializationLifetime.envelope 3 (heapCap s) (binaryWordWidth 3) + 100

theorem input_widths (s : ℕ) (capacity resource : FixedArrayTable 3 SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j))
    (hCapacity : ∀ j,RationalHeight (value (capacity.read j)) s)
    (hResource : ∀ j,RationalHeight (value (resource.read j)) s) :
    (∀ j,width (capacity.read j) ≤ inputWidth s) ∧ (∀ j,width (resource.read j) ≤ inputWidth s) := by
  have hHeight := expressionHeightBudget_ge_input s (3 * 2)
  constructor
  · intro j
    have hw := (hC j).2.trans (rationalWordWidth_of_height (hCapacity j))
    unfold inputWidth BinaryPRGWordControllerBooleanResourceThreeWork.widthBound BinaryThreeResourceHeight.resourceHeight
    omega
  · intro j
    have hw := (hR j).2.trans (rationalWordWidth_of_height (hResource j))
    unfold inputWidth BinaryPRGWordControllerBooleanResourceThreeWork.widthBound BinaryThreeResourceHeight.resourceHeight
    omega

theorem nativeWithTrace_input_usage (s : ℕ) (hs : 2 ≤ s) (seed : BinarySeedLookupTree.Store)
    (capacity resource : FixedArrayTable 3 SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j))
    (hCapacity : ∀ j,RationalHeight (value (capacity.read j)) s)
    (hResource : ∀ j,RationalHeight (value (resource.read j)) s)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    usage (nativeWithTrace seed capacity resource hC hR pc hp).2 ≤ envelope s seed.width seed.cap.value := by
  obtain ⟨hc,hr⟩ := input_widths s capacity resource hC hR hCapacity hResource
  have hW : 1 ≤ inputWidth s := by unfold inputWidth BinaryPRGWordControllerBooleanResourceThreeWork.widthBound; omega
  have hInitial := BinaryPRGHeapInitialLifetimeBound.initialWithTrace_usage capacity resource hC hR _ hW hc hr
  have hLoop : let prepared := BinaryPRGHeapInitialLifetime.initialWithTrace capacity resource hC hR
      usage (BinaryPRGHeapLoopLifetime.runWithTrace seed prepared.1.1
        (BinaryPRGWordControllerBooleanResourceSource.capacityCanonical capacity hC) prepared.1.2 pc hp).2 ≤
      BinaryPRGHeapLifetimePolynomial.threeLoopEnvelope s seed.width seed.cap.value := by
    dsimp only
    rw [BinaryPRGHeapInitialLifetime.initialWithTrace_erasure]
    exact BinaryPRGHeapLifetimePolynomial.original_three_loop_usage s hs seed capacity resource hC hR hCapacity hResource pc hp
  have h := nativeWithTrace_usage seed capacity resource hC hR pc hp _ _ _ hInitial hLoop
    (fun result hSome => returned_heap s hs seed capacity resource hC hR hCapacity hResource pc hp result hSome)
  have hm := BinaryPRGHeapNativeLifetimeBound.materialization_depth_mono 3 (heapCap s)
    (BinaryPRGHeapResourceInputBounds.source_depth capacity)
  unfold envelope
  omega

theorem native_all_prefix (s : ℕ) (hs : 2 ≤ s) (seed : BinarySeedLookupTree.Store)
    (capacity resource : FixedArrayTable 3 SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j))
    (hCapacity : ∀ j,RationalHeight (value (capacity.read j)) s)
    (hResource : ∀ j,RationalHeight (value (resource.read j)) s)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) (borrowed steps : ℕ) :
    retainedHeap borrowed (nativeWithTrace seed capacity resource hC hR pc hp).2 steps ≤
        borrowed + envelope s seed.width seed.cap.value ∧
      framePeak ((nativeWithTrace seed capacity resource hC hR pc hp).2.take steps) ≤ envelope s seed.width seed.cap.value :=
  all_prefix _ _ (nativeWithTrace_input_usage s hs seed capacity resource hC hR hCapacity hResource pc hp) borrowed steps

end Blotto.BinaryPRGHeapThreeNativeLifetimeBound
