import Blotto.BinaryPRGHeapNativeLifetime

/-! Original canonical array/lattice promises derive all initialization, loop
and returned-tape premises of the complete native allocation observer. -/

namespace Blotto.BinaryPRGHeapNativeLifetimeBound
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGHeapTraceUsage BinaryPRGHeapNativeLifetime
open BinaryPRGHeapResourceSource (capStore count)
open BinaryPRGHeapResourceLoop (Finished)
set_option maxHeartbeats 1500000

variable {n : ℕ}

theorem materialization_depth_mono (n H : ℕ) {d e : ℕ} (h : d ≤ e) :
    BinaryPRGHeapMaterializationLifetime.envelope n H d ≤ BinaryPRGHeapMaterializationLifetime.envelope n H e := by
  unfold BinaryPRGHeapMaterializationLifetime.envelope BinaryPRGHeapMaterializationLifetime.rowEnvelope
    BinaryPRGHeapMaterializationLifetime.collectEnvelope BinaryPRGHeapEnumerationLifetime.envelope
    BinaryPRGHeapEnumerationLifetime.localEnvelope BinaryPRGHeapTraceUsage.readEnvelope
    BinaryPRGHeapStoredTree.readBound BinaryPRGWordStoreHeapMachine.lookupBound
    BinaryPRGWordStoreHeapMachine.lookupAllocation BinaryPRGWordStoreHeapMachine.readBound
    BinaryPRGWordStoreHeapMachine.skipBound
  gcongr

def envelope (n W D indexWidth seedCap : ℕ) : ℕ :=
  BinaryPRGHeapInitialLifetimeBound.envelope n W (binaryWordWidth n) +
    BinaryPRGHeapLifetimePolynomial.arrayLoopEnvelope n W D indexWidth seedCap +
    BinaryPRGHeapMaterializationLifetime.envelope n (BinaryPRGHeapResourceInputCost.heapBound n W D) (binaryWordWidth n) + 100

theorem returned_heap (seed : BinarySeedLookupTree.Store) (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j))
    (W D : ℕ) (hW : 1 ≤ W) (hD : 0 < D)
    (hCapacity : ∀ j,width (capacity.read j) ≤ W) (hResource : ∀ j,width (resource.read j) ≤ W)
    (hLattice : ∀ j,OnRationalLattice D (value (capacity.read j)))
    (hBox : ∀ j,0 ≤ value (capacity.read j) ∧ value (capacity.read j) ≤ 1)
    (hRL : ∀ j,OnRationalLattice D (value (resource.read j)))
    (hRB : ∀ j,0 ≤ value (resource.read j) ∧ value (resource.read j) ≤ value (capacity.read j))
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value)
    (state : Finished (capStore capacity) n (count capacity))
    (hSome : (sourceWithTrace seed capacity resource hC hR pc hp).1.2.1 = some state) :
    state.heap.tape.length ≤ BinaryPRGHeapResourceInputCost.heapBound n W D := by
  let prepared := BinaryPRGHeapResourceSource.initialWithWork capacity resource hC hR
  have hInv := BinaryPRGHeapResourceInvariant.initial_lattice capacity resource hC hR D hRL hRB
  have hLat : ∀ j,OnRationalLattice D (value ((BinaryPRGWordControllerBooleanResourceUpdate.table
      (capStore capacity).cap (capStore capacity).tree n (count capacity)).read j)) := by
    rw [BinaryPRGWordControllerBooleanResourceSource.capacityTable]
    exact hLattice
  have hBounds : ∀ j,0 ≤ value ((BinaryPRGWordControllerBooleanResourceUpdate.table
      (capStore capacity).cap (capStore capacity).tree n (count capacity)).read j) ∧
      value ((BinaryPRGWordControllerBooleanResourceUpdate.table
        (capStore capacity).cap (capStore capacity).tree n (count capacity)).read j) ≤ 1 := by
    rw [BinaryPRGWordControllerBooleanResourceSource.capacityTable]
    exact hBox
  rw [sourceWithTrace_erasure] at hSome
  change (BinaryPRGHeapResourceLoop.runWithWork seed prepared.1.1
    (BinaryPRGWordControllerBooleanResourceSource.capacityCanonical capacity hC) prepared.1.2 pc hp).1.1 = some state at hSome
  have hResult := BinaryPRGHeapResourceReservation.runWithWork_source_reserved
    (hC := BinaryPRGWordControllerBooleanResourceSource.capacityCanonical capacity hC)
    D hD hLat hBounds seed prepared.1.1 prepared.1.2 hInv pc hp state hSome
  have hHeap : state.heap.tape.length ≤ BinaryPRGHeapResourceSourceReservation.heapCap capacity resource hC hR D := by
    have h := hResult.2
    change state.heap.tape.length + _ ≤ BinaryPRGHeapResourceSourceReservation.heapCap capacity resource hC hR D at h
    omega
  exact hHeap.trans (BinaryPRGHeapResourceInputCost.source_heapCap_bound capacity resource hC hR W D hW hCapacity hResource)

theorem nativeWithTrace_input_usage (seed : BinarySeedLookupTree.Store) (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j))
    (W D : ℕ) (hW : 1 ≤ W) (hD : 0 < D)
    (hCapacity : ∀ j,width (capacity.read j) ≤ W) (hResource : ∀ j,width (resource.read j) ≤ W)
    (hLattice : ∀ j,OnRationalLattice D (value (capacity.read j)))
    (hBox : ∀ j,0 ≤ value (capacity.read j) ∧ value (capacity.read j) ≤ 1)
    (hRL : ∀ j,OnRationalLattice D (value (resource.read j)))
    (hRB : ∀ j,0 ≤ value (resource.read j) ∧ value (resource.read j) ≤ value (capacity.read j))
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    usage (nativeWithTrace seed capacity resource hC hR pc hp).2 ≤ envelope n W D seed.width seed.cap.value := by
  have hInitial := BinaryPRGHeapInitialLifetimeBound.initialWithTrace_usage capacity resource hC hR W hW hCapacity hResource
  have hLoop : let prepared := BinaryPRGHeapInitialLifetime.initialWithTrace capacity resource hC hR
      usage (BinaryPRGHeapLoopLifetime.runWithTrace seed prepared.1.1
        (BinaryPRGWordControllerBooleanResourceSource.capacityCanonical capacity hC) prepared.1.2 pc hp).2 ≤
      BinaryPRGHeapLifetimePolynomial.arrayLoopEnvelope n W D seed.width seed.cap.value := by
    dsimp only
    rw [BinaryPRGHeapInitialLifetime.initialWithTrace_erasure]
    exact BinaryPRGHeapLifetimePolynomial.original_array_loop_usage seed capacity resource hC hR W D hW hD
      hCapacity hResource hLattice hBox hRL hRB pc hp
  have h := nativeWithTrace_usage seed capacity resource hC hR pc hp _ _ _ hInitial hLoop
    (fun state hSome => returned_heap seed capacity resource hC hR W D hW hD hCapacity hResource
      hLattice hBox hRL hRB pc hp state hSome)
  have hm := materialization_depth_mono n (BinaryPRGHeapResourceInputCost.heapBound n W D)
    (BinaryPRGHeapResourceInputBounds.source_depth capacity)
  unfold envelope
  omega

theorem native_all_prefix (seed : BinarySeedLookupTree.Store) (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j))
    (W D : ℕ) (hW : 1 ≤ W) (hD : 0 < D)
    (hCapacity : ∀ j,width (capacity.read j) ≤ W) (hResource : ∀ j,width (resource.read j) ≤ W)
    (hLattice : ∀ j,OnRationalLattice D (value (capacity.read j)))
    (hBox : ∀ j,0 ≤ value (capacity.read j) ∧ value (capacity.read j) ≤ 1)
    (hRL : ∀ j,OnRationalLattice D (value (resource.read j)))
    (hRB : ∀ j,0 ≤ value (resource.read j) ∧ value (resource.read j) ≤ value (capacity.read j))
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) (borrowed steps : ℕ) :
    retainedHeap borrowed (nativeWithTrace seed capacity resource hC hR pc hp).2 steps ≤
        borrowed + envelope n W D seed.width seed.cap.value ∧
      framePeak ((nativeWithTrace seed capacity resource hC hR pc hp).2.take steps) ≤ envelope n W D seed.width seed.cap.value :=
  all_prefix _ _ (nativeWithTrace_input_usage seed capacity resource hC hR W D hW hD hCapacity hResource hLattice hBox hRL hRB pc hp) borrowed steps

end Blotto.BinaryPRGHeapNativeLifetimeBound
