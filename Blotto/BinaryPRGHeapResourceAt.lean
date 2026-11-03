import Blotto.BinaryPRGHeapResourceSourceReservation
import Blotto.BinaryPRGWordControllerBooleanResourceSourceWork

/-! The physical original-array resource runner can begin at an existing
absolute Boolean seed cursor. Its source and terminal retain the same cap word
and refine the native general resource run at that cursor. -/

namespace Blotto.BinaryPRGHeapResourceAt
open BinaryRationalNormalization BinaryRationalEncoding
open BinaryPRGHeapResourceLoop (Finished)

variable {n : ℕ}

def sourceAt (seed : BinarySeedLookupTree.Store) (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j))
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (FixedBinaryWord (BinaryPRGHeapResourceSource.capStore capacity).width ×
      BinaryPRGHeapResourceLoop.Result seed (BinaryPRGHeapResourceSource.capStore capacity)
        n (BinaryPRGHeapResourceSource.count capacity)) × ℕ :=
  let prepared := BinaryPRGHeapResourceSource.initialWithWork capacity resource hC hR
  let capWord : FixedBinaryWord (BinaryPRGHeapResourceSource.capStore capacity).width :=
    ⟨prepared.1.1.ruler,prepared.1.1.size⟩
  let completed := BinaryPRGHeapResourceLoop.runWithWork seed prepared.1.1
    (BinaryPRGWordControllerBooleanResourceSource.capacityCanonical capacity hC)
    prepared.1.2 pc hp
  ((capWord,completed.1),prepared.2 + completed.2 + 3)

theorem sourceAt_cap (seed : BinarySeedLookupTree.Store) (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j))
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (sourceAt seed capacity resource hC hR pc hp).1.1 =
      (BinaryPRGHeapResourceSource.capStore capacity).cap := by
  rfl

theorem sourceAt_original (seed : BinarySeedLookupTree.Store)
    (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j))
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    BinaryPRGWordControllerBooleanResourceSource.result capacity seed
      (sourceAt seed capacity resource hC hR pc hp).1.2.reference =
      BinaryPRGWordControllerResource.run seed capacity hC
        (BinaryResourcePair.initial capacity resource hC hR) pc hp := by
  unfold sourceAt
  dsimp only
  rw [BinaryPRGHeapResourceLoop.runWithWork_value,
    BinaryPRGHeapResourceSource.initialWithWork_reference,
    BinaryPRGWordControllerBooleanResourceSource.result_reference,
    BinaryPRGWordControllerBooleanResourceLoop.run_original,
    BinaryPRGWordControllerBooleanResourceSource.run_transport _ _ capacity _ _ hC,
    BinaryPRGWordControllerBooleanResourceSource.initial_reference]

def nativeAt (seed : BinarySeedLookupTree.Store) (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j))
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    BinaryPRGWordControllerResource.Result seed capacity × ℕ :=
  let drawn := sourceAt seed capacity resource hC hR pc hp
  match drawn.1.2.1 with
  | none => ((none,drawn.1.2.2),drawn.2 + 2)
  | some state =>
      let terminal := BinaryPRGHeapResourceMaterialization.materializeWithWork capacity
        (BinaryPRGWordControllerBooleanResourceSource.capacityTable capacity)
        drawn.1.1 (sourceAt_cap seed capacity resource hC hR pc hp) state
      ((some terminal.1,drawn.1.2.2),drawn.2 + terminal.2 + 4)

theorem nativeAt_erasure (seed : BinarySeedLookupTree.Store)
    (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j))
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (nativeAt seed capacity resource hC hR pc hp).1 =
      BinaryPRGWordControllerResource.run seed capacity hC
        (BinaryResourcePair.initial capacity resource hC hR) pc hp := by
  have hSource := sourceAt_original seed capacity resource hC hR pc hp
  unfold nativeAt
  dsimp only
  cases hOutput : (sourceAt seed capacity resource hC hR pc hp).1.2.1 with
  | none =>
      simpa only [hOutput,BinaryPRGWordControllerBooleanResourceSource.result,
        BinaryPRGHeapResourceLoop.Result.reference,Option.map_none] using hSource
  | some state =>
      have ht := BinaryPRGHeapResourceMaterialization.materializeSource_reference capacity
        (sourceAt seed capacity resource hC hR pc hp).1.1
        (sourceAt_cap seed capacity resource hC hR pc hp) state
      simp only [hOutput,BinaryPRGWordControllerBooleanResourceSource.result,
        BinaryPRGHeapResourceLoop.Result.reference,Option.map_some] at hSource
      simpa only [ht] using hSource

theorem nativeAt_bound (seed : BinarySeedLookupTree.Store)
    (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j))
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value)
    (I M H : ℕ)
    (hInitial : (BinaryPRGHeapResourceSource.initialWithWork capacity resource hC hR).2 ≤ I)
    (hLoop : (BinaryPRGHeapResourceLoop.runWithWork seed
      (BinaryPRGHeapResourceSource.initialWithWork capacity resource hC hR).1.1
      (BinaryPRGWordControllerBooleanResourceSource.capacityCanonical capacity hC)
      (BinaryPRGHeapResourceSource.initialWithWork capacity resource hC hR).1.2 pc hp).2 ≤ M)
    (hHeap : ∀ state : Finished (BinaryPRGHeapResourceSource.capStore capacity) n
        (BinaryPRGHeapResourceSource.count capacity),
      (sourceAt seed capacity resource hC hR pc hp).1.2.1 = some state → state.heap.tape.length ≤ H) :
    (nativeAt seed capacity resource hC hR pc hp).2 ≤ I + M +
      BinaryPRGHeapResourceSourceReservation.terminalBound n
        (BinaryPRGHeapResourceSource.capStore capacity).width H + 7 := by
  have hSource : (sourceAt seed capacity resource hC hR pc hp).2 ≤ I + M + 3 := by
    unfold sourceAt
    dsimp only
    omega
  unfold nativeAt
  dsimp only
  cases hResult : (sourceAt seed capacity resource hC hR pc hp).1.2.1 with
  | none => dsimp only; omega
  | some state =>
      dsimp only
      have hTerminal := BinaryPRGHeapResourceMaterialization.materializeWithWork_uniformBound
        capacity (BinaryPRGWordControllerBooleanResourceSource.capacityTable capacity)
        (sourceAt seed capacity resource hC hR pc hp).1.1
        (sourceAt_cap seed capacity resource hC hR pc hp) state
      have ht := BinaryPRGHeapResourceSourceReservation.terminalUniformBound_le
        (sourceAt seed capacity resource hC hR pc hp).1.1
        (sourceAt_cap seed capacity resource hC hR pc hp) state H (hHeap state hResult)
      omega

end Blotto.BinaryPRGHeapResourceAt
