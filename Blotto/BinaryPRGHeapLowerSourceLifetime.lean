import Blotto.BinaryPRGHeapLowerLifetimeBound
import Blotto.BinaryPRGHeapNativeLifetime

/-! Complete deterministic lower resource execution starts from original stored
arrays, builds and scans their physical heaps, follows the lower tape loop and
materializes the returned native words/active list. It has no seed input. -/
namespace Blotto.BinaryPRGHeapLowerSourceLifetime
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGHeapTraceUsage
open BinaryPRGHeapResourceSource (capStore count)
open BinaryPRGHeapResourceLoop (Finished)
open BinaryPRGWordControllerBooleanResourceSource (transport)
set_option maxHeartbeats 2000000
variable {n : ℕ}

private theorem word_ext {w : ℕ} (a b : FixedBinaryWord w) (h : a.bits = b.bits) : a = b := by
  cases a
  cases b
  cases h
  rfl

def sourceWithTrace (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j)) :
    (FixedBinaryWord (capStore capacity).width × Finished (capStore capacity) n (count capacity)) × Trace :=
  let prepared := BinaryPRGHeapInitialLifetime.initialWithTrace capacity resource hC hR
  let capWord : FixedBinaryWord (capStore capacity).width := ⟨prepared.1.1.ruler,prepared.1.1.size⟩
  let completed := BinaryPRGHeapLowerLifetime.runWithTrace prepared.1.1
    (BinaryPRGWordControllerBooleanResourceSource.capacityCanonical capacity hC) prepared.1.2
  ((capWord,completed.1),wrap 32 2 [prepared.2,completed.2])

theorem sourceWithTrace_cap (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j)) :
    (sourceWithTrace capacity resource hC hR).1.1 = (capStore capacity).cap := by
  unfold sourceWithTrace
  dsimp only
  apply word_ext
  change (BinaryPRGHeapInitialLifetime.initialWithTrace capacity resource hC hR).1.1.ruler = _
  rw [BinaryPRGHeapInitialLifetime.initialWithTrace_erasure]
  rfl

theorem choose_transport (first second : FixedArrayTable n SignedWord) (h : first = second)
    (hC : ∀ j,CanonicalWord (first.read j)) (hD : ∀ j,CanonicalWord (second.read j))
    (state : BinaryResourcePair.Certified first) :
    transport h (BinaryGeneralResourceFallback.choose hC state) =
      BinaryGeneralResourceFallback.choose hD (transport h state) := by
  subst second
  rfl

theorem sourceWithTrace_reference (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j)) :
    transport (BinaryPRGWordControllerBooleanResourceSource.capacityTable capacity)
      (sourceWithTrace capacity resource hC hR).1.2.reference.reference =
      BinaryGeneralResourceFallback.choose hC (BinaryResourcePair.initial capacity resource hC hR) := by
  unfold sourceWithTrace
  dsimp only
  rw [BinaryPRGHeapLowerLifetime.runWithTrace_reference,choose_transport _ _ _ _ hC,
    BinaryPRGHeapInitialLifetime.initialWithTrace_reference,
    BinaryPRGWordControllerBooleanResourceSource.initial_reference]

def nativeWithTrace (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j)) :
    BinaryResourcePair.Certified capacity × Trace :=
  let drawn := sourceWithTrace capacity resource hC hR
  let terminal := BinaryPRGHeapMaterializationLifetime.materializeWithTrace capacity
    (BinaryPRGWordControllerBooleanResourceSource.capacityTable capacity)
    drawn.1.1 (sourceWithTrace_cap capacity resource hC hR) drawn.1.2
  (terminal.1,wrap 24 2 [drawn.2,terminal.2])

theorem nativeWithTrace_erasure (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j)) :
    (nativeWithTrace capacity resource hC hR).1 =
      BinaryGeneralResourceFallback.choose hC (BinaryResourcePair.initial capacity resource hC hR) := by
  unfold nativeWithTrace
  dsimp only
  rw [BinaryPRGHeapMaterializationLifetime.materializeWithTrace_erasure,
    BinaryPRGHeapResourceMaterialization.materializeWithWork_reference,
    BinaryPRGWordControllerBooleanResourceSource.materializeTo_reference]
  exact sourceWithTrace_reference capacity resource hC hR

theorem sourceWithTrace_usage (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j)) (I L : ℕ)
    (hI : usage (BinaryPRGHeapInitialLifetime.initialWithTrace capacity resource hC hR).2 ≤ I)
    (hL : let prepared := BinaryPRGHeapInitialLifetime.initialWithTrace capacity resource hC hR
      usage (BinaryPRGHeapLowerLifetime.runWithTrace prepared.1.1
        (BinaryPRGWordControllerBooleanResourceSource.capacityCanonical capacity hC) prepared.1.2).2 ≤ L) :
    usage (sourceWithTrace capacity resource hC hR).2 ≤ I+L+38 := by
  let prepared := BinaryPRGHeapInitialLifetime.initialWithTrace capacity resource hC hR
  let completed := BinaryPRGHeapLowerLifetime.runWithTrace prepared.1.1
    (BinaryPRGWordControllerBooleanResourceSource.capacityCanonical capacity hC) prepared.1.2
  have hw := wrap_usage 32 2 [prepared.2,completed.2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change usage (wrap 32 2 [prepared.2,completed.2]) ≤ _
  change usage prepared.2 ≤ I at hI
  change usage completed.2 ≤ L at hL
  omega

theorem nativeWithTrace_usage (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j)) (I L H : ℕ)
    (hI : usage (BinaryPRGHeapInitialLifetime.initialWithTrace capacity resource hC hR).2 ≤ I)
    (hL : let prepared := BinaryPRGHeapInitialLifetime.initialWithTrace capacity resource hC hR
      usage (BinaryPRGHeapLowerLifetime.runWithTrace prepared.1.1
        (BinaryPRGWordControllerBooleanResourceSource.capacityCanonical capacity hC) prepared.1.2).2 ≤ L)
    (hHeap : (sourceWithTrace capacity resource hC hR).1.2.heap.tape.length ≤ H) :
    usage (nativeWithTrace capacity resource hC hR).2 ≤ I+L+
      BinaryPRGHeapMaterializationLifetime.envelope n H (capStore capacity).width+100 := by
  have hSource := sourceWithTrace_usage capacity resource hC hR I L hI hL
  let drawn := sourceWithTrace capacity resource hC hR
  have ht := BinaryPRGHeapMaterializationLifetime.materializeWithTrace_usage capacity
    (BinaryPRGWordControllerBooleanResourceSource.capacityTable capacity)
    drawn.1.1 (sourceWithTrace_cap capacity resource hC hR) drawn.1.2 H hHeap
  change _ ≤ BinaryPRGHeapMaterializationLifetime.envelope n H (capStore capacity).width at ht
  have hw := wrap_usage 24 2 [drawn.2,
    (BinaryPRGHeapMaterializationLifetime.materializeWithTrace capacity
      (BinaryPRGWordControllerBooleanResourceSource.capacityTable capacity)
      drawn.1.1 (sourceWithTrace_cap capacity resource hC hR) drawn.1.2).2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change usage (nativeWithTrace capacity resource hC hR).2 ≤ _ at hw
  change usage drawn.2 ≤ _ at hSource
  omega

end Blotto.BinaryPRGHeapLowerSourceLifetime
