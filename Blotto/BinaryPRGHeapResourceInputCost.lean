import Blotto.BinaryPRGHeapResourceInputBounds

/-! Substitute original word widths and dimensions into the physical resource
source/loop/native-terminal work bound. The resulting envelope has no reached
heap sizes or preparation executions as arguments. -/

namespace Blotto.BinaryPRGHeapResourceInputCost
open BinaryRationalNormalization BinaryRationalEncoding
open BinaryPRGHeapResourceInputBounds (initialHeapBound preparationBound readBound_mono scanBound_mono)

theorem patchBound_mono {a b i j : ℕ} (hCells : a ≤ b) (hDepth : i ≤ j) :
    BinaryPRGWordStoreHeapMachine.patchBound a i ≤
      BinaryPRGWordStoreHeapMachine.patchBound b j := by
  have hw := binaryWordWidth_mono hCells
  unfold BinaryPRGWordStoreHeapMachine.patchBound BinaryPRGWordStoreHeapMachine.readBound
    BinaryPRGWordStoreHeapMachine.skipBound BinaryPRGWordStoreHeapMachine.allocationBound
  gcongr

theorem updateBound_mono {C H depth C' H' depth' W count : ℕ}
    (hC : C ≤ C') (hH : H ≤ H') (hDepth : depth ≤ depth') :
    BinaryPRGHeapResourceUpdateBudget.updateBound C H depth W count ≤
      BinaryPRGHeapResourceUpdateBudget.updateBound C' H' depth' W count := by
  have hr := readBound_mono hH hDepth
  have hp := patchBound_mono hH hDepth
  have hs := scanBound_mono (W := W) (count := 2) hC hH hDepth
  have ha := Nat.mul_le_mul_right (count + 2)
    (Nat.mul_le_mul_left 2 (Nat.add_le_add_right hDepth 1))
  unfold BinaryPRGHeapResourceUpdateBudget.updateBound
  omega

theorem pairBound_mono {C H depth C' H' depth' D seedWidth seedCap : ℕ}
    (hC : C ≤ C') (hH : H ≤ H') (hDepth : depth ≤ depth') :
    BinaryPRGHeapResourceReservation.pairBound D depth seedWidth seedCap C H ≤
      BinaryPRGHeapResourceReservation.pairBound D depth' seedWidth seedCap C' H' := by
  have hc := readBound_mono hC hDepth
  have hh := readBound_mono hH hDepth
  unfold BinaryPRGHeapResourceReservation.pairBound
    BinaryPRGWordControllerBooleanResourcePair.bound
  omega

theorem stepBound_mono {C H depth C' H' depth' count D seedWidth seedCap : ℕ}
    (hC : C ≤ C') (hH : H ≤ H') (hDepth : depth ≤ depth') :
    BinaryPRGHeapResourceReservation.stepBound count D depth seedWidth seedCap C H ≤
      BinaryPRGHeapResourceReservation.stepBound count D depth' seedWidth seedCap C' H' :=
  max_le_max (pairBound_mono hC hH hDepth) (updateBound_mono hC hH hDepth)

theorem sourceHeapCap_mono {cells cells' depth depth' count W : ℕ}
    (hCells : cells ≤ cells') (hDepth : depth ≤ depth') :
    BinaryPRGHeapResourceReservation.sourceHeapCap cells count depth W ≤
      BinaryPRGHeapResourceReservation.sourceHeapCap cells' count depth' W := by
  apply BinaryPRGWordStoreHeap.heapBound_mono
  unfold BinaryPRGHeapResourceReservation.sourceSize
  gcongr

theorem terminalBound_mono {depth depth' H H' count : ℕ}
    (hDepth : depth ≤ depth') (hH : H ≤ H') :
    BinaryPRGHeapResourceSourceReservation.terminalBound count depth H ≤
      BinaryPRGHeapResourceSourceReservation.terminalBound count depth' H' := by
  have hr := readBound_mono hH hDepth
  unfold BinaryPRGHeapResourceSourceReservation.terminalBound
  gcongr

def heapBound (count W D : ℕ) : ℕ :=
  BinaryPRGHeapResourceReservation.sourceHeapCap (initialHeapBound count W)
    count (binaryWordWidth count) (BinaryPRGWordControllerBooleanResourceLoopWork.widthBound D)

def loopBound (count W D seedWidth seedCap : ℕ) : ℕ :=
  count * (2 * BinaryPRGHeapResourceReservation.stepBound count D
    (binaryWordWidth count) seedWidth seedCap (initialHeapBound count W)
    (heapBound count W D)) + 2

def nativeBound (count W D seedWidth seedCap : ℕ) : ℕ :=
  preparationBound count W + loopBound count W D seedWidth seedCap +
    BinaryPRGHeapResourceSourceReservation.terminalBound count (binaryWordWidth count)
      (heapBound count W D) + 7

variable {n : ℕ}

theorem source_heapCap_bound (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j))
    (hR : ∀ j,CanonicalWord (resource.read j)) (W D : ℕ) (hW : 1 ≤ W)
    (hCapacity : ∀ j,width (capacity.read j) ≤ W)
    (hResource : ∀ j,width (resource.read j) ≤ W) :
    BinaryPRGHeapResourceSourceReservation.heapCap capacity resource hC hR D ≤
      heapBound n W D :=
  sourceHeapCap_mono
    (BinaryPRGHeapResourceInputBounds.initial_heaps_bound capacity resource hC hR
      W hW hCapacity hResource).2
    (BinaryPRGHeapResourceInputBounds.source_depth capacity)

theorem source_loopBound_le (seed : BinarySeedLookupTree.Store)
    (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j))
    (hR : ∀ j,CanonicalWord (resource.read j)) (W D : ℕ) (hW : 1 ≤ W)
    (hCapacity : ∀ j,width (capacity.read j) ≤ W)
    (hResource : ∀ j,width (resource.read j) ≤ W) :
    BinaryPRGHeapResourceSourceReservation.loopBound seed capacity resource hC hR D ≤
      loopBound n W D seed.width seed.cap.value := by
  have hHeap := source_heapCap_bound capacity resource hC hR W D hW hCapacity hResource
  have hInitial := (BinaryPRGHeapResourceInputBounds.initial_heaps_bound
    capacity resource hC hR W hW hCapacity hResource).1
  have hd := BinaryPRGHeapResourceInputBounds.source_depth capacity
  exact Nat.add_le_add_right (Nat.mul_le_mul_left n
    (Nat.mul_le_mul_left 2 (stepBound_mono hInitial hHeap hd))) 2

theorem runNativeWithWork_input_bound (seed : BinarySeedLookupTree.Store)
    (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j))
    (hR : ∀ j,CanonicalWord (resource.read j)) (W D : ℕ) (hW : 1 ≤ W) (hD : 0 < D)
    (hCapacity : ∀ j,width (capacity.read j) ≤ W)
    (hResource : ∀ j,width (resource.read j) ≤ W)
    (hLattice : ∀ j,OnRationalLattice D (value (capacity.read j)))
    (hBox : ∀ j,0 ≤ value (capacity.read j) ∧ value (capacity.read j) ≤ 1)
    (hResourceLattice : ∀ j,OnRationalLattice D (value (resource.read j)))
    (hResourceBox : ∀ j,0 ≤ value (resource.read j) ∧
      value (resource.read j) ≤ value (capacity.read j)) :
    (BinaryPRGHeapResourceMaterialization.runNativeWithWork
      seed capacity resource hC hR).2 ≤ nativeBound n W D seed.width seed.cap.value := by
  have hNative := BinaryPRGHeapResourceSourceReservation.runNativeWithWork_bound
    seed capacity resource hC hR D hD hLattice hBox hResourceLattice hResourceBox
  have hPrep := BinaryPRGHeapResourceInputBounds.initialWorkEnvelope_input_bound
    capacity resource W hW hCapacity hResource
  have hLoop := source_loopBound_le seed capacity resource hC hR W D hW hCapacity hResource
  have hHeap := source_heapCap_bound capacity resource hC hR W D hW hCapacity hResource
  have hTerminal := terminalBound_mono (count := n)
    (BinaryPRGHeapResourceInputBounds.source_depth capacity) hHeap
  unfold nativeBound
  omega

theorem returned_heap_input_bound (seed : BinarySeedLookupTree.Store)
    (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j))
    (hR : ∀ j,CanonicalWord (resource.read j)) (W D : ℕ) (hW : 1 ≤ W) (hD : 0 < D)
    (hCapacity : ∀ j,width (capacity.read j) ≤ W)
    (hResource : ∀ j,width (resource.read j) ≤ W)
    (hLattice : ∀ j,OnRationalLattice D (value (capacity.read j)))
    (hBox : ∀ j,0 ≤ value (capacity.read j) ∧ value (capacity.read j) ≤ 1)
    (hResourceLattice : ∀ j,OnRationalLattice D (value (resource.read j)))
    (hResourceBox : ∀ j,0 ≤ value (resource.read j) ∧
      value (resource.read j) ≤ value (capacity.read j))
    (result : BinaryPRGHeapResourceLoop.Finished
      (BinaryPRGHeapResourceSource.capStore capacity) n (BinaryPRGHeapResourceSource.count capacity))
    (hSome : (BinaryPRGHeapResourceSource.runWithRetainedCap
      seed capacity resource hC hR).1.2.1 = some result) :
    result.heap.tape.length ≤ heapBound n W D :=
  (BinaryPRGHeapResourceSourceReservation.returned_heap_bound
    seed capacity resource hC hR D hD hLattice hBox hResourceLattice hResourceBox result hSome).trans
    (source_heapCap_bound capacity resource hC hR W D hW hCapacity hResource)

end Blotto.BinaryPRGHeapResourceInputCost
