import Blotto.BinaryPRGHeapResourceReservation
import Blotto.BinaryPRGHeapResourceMaterialization

/-! The original array source instantiates the physical resource reservation.
The resulting native work bound has no per-step price or heap-preservation
oracle; its initial preparation envelope and heap sizes remain explicit. -/

namespace Blotto.BinaryPRGHeapResourceSourceReservation
open BinaryRationalNormalization BinaryRationalEncoding
open BinaryPRGHeapResourceLoop (Finished)

variable {n : ℕ}

def heapCap (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j))
    (hR : ∀ j,CanonicalWord (resource.read j)) (D : ℕ) : ℕ :=
  BinaryPRGHeapResourceReservation.sourceHeapCap
    (BinaryPRGHeapResourceSource.initialWithWork capacity resource hC hR).1.2.heap.tape.length
    n (BinaryPRGHeapResourceSource.capStore capacity).width
    (BinaryPRGWordControllerBooleanResourceLoopWork.widthBound D)

def loopBound (seed : BinarySeedLookupTree.Store)
    (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j))
    (hR : ∀ j,CanonicalWord (resource.read j)) (D : ℕ) : ℕ :=
  n * (2 * BinaryPRGHeapResourceReservation.stepBound n D
    (BinaryPRGHeapResourceSource.capStore capacity).width seed.width seed.cap.value
    (BinaryPRGHeapResourceSource.initialWithWork capacity resource hC hR).1.1.heap.tape.length
    (heapCap capacity resource hC hR D)) + 2

theorem runWithRetainedCap_bound (seed : BinarySeedLookupTree.Store)
    (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j))
    (hR : ∀ j,CanonicalWord (resource.read j)) (D : ℕ) (hD : 0 < D)
    (hLattice : ∀ j,OnRationalLattice D (value (capacity.read j)))
    (hBox : ∀ j,0 ≤ value (capacity.read j) ∧ value (capacity.read j) ≤ 1)
    (hResourceLattice : ∀ j,OnRationalLattice D (value (resource.read j)))
    (hResourceBox : ∀ j,0 ≤ value (resource.read j) ∧
      value (resource.read j) ≤ value (capacity.read j)) :
    (BinaryPRGHeapResourceSource.runWithRetainedCap seed capacity resource hC hR).2 ≤
      BinaryPRGHeapResourceSource.initialWorkEnvelope capacity resource +
        loopBound seed capacity resource hC hR D + 3 := by
  let prepared := BinaryPRGHeapResourceSource.initialWithWork capacity resource hC hR
  have hs := BinaryPRGHeapResourceInvariant.initial_lattice
    capacity resource hC hR D hResourceLattice hResourceBox
  have hl : ∀ j,OnRationalLattice D
      (value ((BinaryPRGWordControllerBooleanResourceUpdate.table
        (BinaryPRGHeapResourceSource.capStore capacity).cap
        (BinaryPRGHeapResourceSource.capStore capacity).tree n
        (BinaryPRGHeapResourceSource.count capacity)).read j)) := by
    rw [BinaryPRGWordControllerBooleanResourceSource.capacityTable]
    exact hLattice
  have hb : ∀ j,0 ≤ value ((BinaryPRGWordControllerBooleanResourceUpdate.table
        (BinaryPRGHeapResourceSource.capStore capacity).cap
        (BinaryPRGHeapResourceSource.capStore capacity).tree n
        (BinaryPRGHeapResourceSource.count capacity)).read j) ∧
      value ((BinaryPRGWordControllerBooleanResourceUpdate.table
        (BinaryPRGHeapResourceSource.capStore capacity).cap
        (BinaryPRGHeapResourceSource.capStore capacity).tree n
        (BinaryPRGHeapResourceSource.count capacity)).read j) ≤ 1 := by
    rw [BinaryPRGWordControllerBooleanResourceSource.capacityTable]
    exact hBox
  have hLoop := BinaryPRGHeapResourceReservation.runWithWork_source_bound
    (hC := BinaryPRGWordControllerBooleanResourceSource.capacityCanonical capacity hC)
    D hD hl hb seed prepared.1.1 prepared.1.2 hs
    (BinaryWordIndexCoinController.zeroIndex seed)
    (by rw [BinaryWordIndexCoinController.zeroIndex_value]; exact Nat.zero_le _)
  have hInitial := BinaryPRGHeapResourceSource.initialWithWork_bound capacity resource hC hR
  change (BinaryPRGHeapResourceLoop.runWithWork seed prepared.1.1
    (BinaryPRGWordControllerBooleanResourceSource.capacityCanonical capacity hC)
    prepared.1.2 (BinaryWordIndexCoinController.zeroIndex seed)
    (by rw [BinaryWordIndexCoinController.zeroIndex_value]; exact Nat.zero_le _)).2 ≤
      loopBound seed capacity resource hC hR D at hLoop
  unfold BinaryPRGHeapResourceSource.runWithRetainedCap
  dsimp only
  change prepared.2 + (BinaryPRGHeapResourceLoop.runWithWork seed prepared.1.1
    (BinaryPRGWordControllerBooleanResourceSource.capacityCanonical capacity hC)
    prepared.1.2 (BinaryWordIndexCoinController.zeroIndex seed)
    (by rw [BinaryWordIndexCoinController.zeroIndex_value]; exact Nat.zero_le _)).2 + 3 ≤ _
  change prepared.2 ≤ _ at hInitial
  omega

theorem returned_heap_bound (seed : BinarySeedLookupTree.Store)
    (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j))
    (hR : ∀ j,CanonicalWord (resource.read j)) (D : ℕ) (hD : 0 < D)
    (hLattice : ∀ j,OnRationalLattice D (value (capacity.read j)))
    (hBox : ∀ j,0 ≤ value (capacity.read j) ∧ value (capacity.read j) ≤ 1)
    (hResourceLattice : ∀ j,OnRationalLattice D (value (resource.read j)))
    (hResourceBox : ∀ j,0 ≤ value (resource.read j) ∧
      value (resource.read j) ≤ value (capacity.read j))
    (result : Finished (BinaryPRGHeapResourceSource.capStore capacity) n
      (BinaryPRGHeapResourceSource.count capacity))
    (hSome : (BinaryPRGHeapResourceSource.runWithRetainedCap
      seed capacity resource hC hR).1.2.1 = some result) :
    result.heap.tape.length ≤ heapCap capacity resource hC hR D := by
  let prepared := BinaryPRGHeapResourceSource.initialWithWork capacity resource hC hR
  have hs := BinaryPRGHeapResourceInvariant.initial_lattice
    capacity resource hC hR D hResourceLattice hResourceBox
  have hl : ∀ j,OnRationalLattice D
      (value ((BinaryPRGWordControllerBooleanResourceUpdate.table
        (BinaryPRGHeapResourceSource.capStore capacity).cap
        (BinaryPRGHeapResourceSource.capStore capacity).tree n
        (BinaryPRGHeapResourceSource.count capacity)).read j)) := by
    rw [BinaryPRGWordControllerBooleanResourceSource.capacityTable]
    exact hLattice
  have hb : ∀ j,0 ≤ value ((BinaryPRGWordControllerBooleanResourceUpdate.table
        (BinaryPRGHeapResourceSource.capStore capacity).cap
        (BinaryPRGHeapResourceSource.capStore capacity).tree n
        (BinaryPRGHeapResourceSource.count capacity)).read j) ∧
      value ((BinaryPRGWordControllerBooleanResourceUpdate.table
        (BinaryPRGHeapResourceSource.capStore capacity).cap
        (BinaryPRGHeapResourceSource.capStore capacity).tree n
        (BinaryPRGHeapResourceSource.count capacity)).read j) ≤ 1 := by
    rw [BinaryPRGWordControllerBooleanResourceSource.capacityTable]
    exact hBox
  have hResult := BinaryPRGHeapResourceReservation.runWithWork_source_reserved
    (hC := BinaryPRGWordControllerBooleanResourceSource.capacityCanonical capacity hC)
    D hD hl hb seed prepared.1.1 prepared.1.2 hs
    (BinaryWordIndexCoinController.zeroIndex seed)
    (by rw [BinaryWordIndexCoinController.zeroIndex_value]; exact Nat.zero_le _)
    result hSome
  have h := hResult.2
  change result.heap.tape.length + _ ≤ heapCap capacity resource hC hR D at h
  omega

def terminalBound (count depth H : ℕ) : ℕ :=
  count * (20 * (depth + 1) + 4) + 12 * (depth + 1) + 1 +
    count * (BinaryPRGHeapStoredTree.readBound H depth + 2 * (depth + 1) + 3) +
    4 + count + 2 + count * (depth + 1) + 5

theorem terminalUniformBound_le {capacity : BinaryPRGWordControllerWordStore.Store}
    {count : ℕ} {hCount : count = capacity.cap.value}
    (capWord : FixedBinaryWord capacity.width) (hCap : capWord = capacity.cap)
    (state : Finished capacity count hCount) (H : ℕ) (hH : state.heap.tape.length ≤ H) :
    BinaryPRGHeapResourceMaterialization.terminalUniformBound capWord state ≤
      terminalBound count capacity.width H := by
  have hValue : capWord.value = count := by rw [hCap,← hCount]
  have hRead := BinaryPRGHeapResourceCoinBudget.readBound_mono
    (depth := capacity.width) hH
  have hm := Nat.mul_le_mul_left count (Nat.add_le_add_right hRead
    (2 * (capacity.width + 1) + 3))
  unfold BinaryPRGHeapResourceMaterialization.terminalUniformBound terminalBound
  rw [hValue]
  simp only [Nat.add_assoc] at hm ⊢
  omega

theorem runNativeWithWork_bound (seed : BinarySeedLookupTree.Store)
    (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j))
    (hR : ∀ j,CanonicalWord (resource.read j)) (D : ℕ) (hD : 0 < D)
    (hLattice : ∀ j,OnRationalLattice D (value (capacity.read j)))
    (hBox : ∀ j,0 ≤ value (capacity.read j) ∧ value (capacity.read j) ≤ 1)
    (hResourceLattice : ∀ j,OnRationalLattice D (value (resource.read j)))
    (hResourceBox : ∀ j,0 ≤ value (resource.read j) ∧
      value (resource.read j) ≤ value (capacity.read j)) :
    (BinaryPRGHeapResourceMaterialization.runNativeWithWork
      seed capacity resource hC hR).2 ≤
      BinaryPRGHeapResourceSource.initialWorkEnvelope capacity resource +
        loopBound seed capacity resource hC hR D +
        terminalBound n (BinaryPRGHeapResourceSource.capStore capacity).width
          (heapCap capacity resource hC hR D) + 7 := by
  have hSource := runWithRetainedCap_bound seed capacity resource hC hR D hD
    hLattice hBox hResourceLattice hResourceBox
  cases hResult : (BinaryPRGHeapResourceSource.runWithRetainedCap
      seed capacity resource hC hR).1.2.1 with
  | none =>
      have hNative := BinaryPRGHeapResourceMaterialization.runNativeWithWork_none_bound
        seed capacity resource hC hR hResult
      omega
  | some result =>
      have hHeap := returned_heap_bound seed capacity resource hC hR D hD
        hLattice hBox hResourceLattice hResourceBox result hResult
      have hTerminal := terminalUniformBound_le _
        (BinaryPRGHeapResourceSource.runWithRetainedCap_cap seed capacity resource hC hR)
        result _ hHeap
      have hNative := BinaryPRGHeapResourceMaterialization.runNativeWithWork_some_bound
        seed capacity resource hC hR result hResult
      omega

end Blotto.BinaryPRGHeapResourceSourceReservation
