import Blotto.BinaryHeapLoopPrimitiveMeasured
import Blotto.BinaryPRGHeapNativeLifetime
import Blotto.BinaryReflectedInitialFused
import Blotto.BinaryHeapMaterializationMeasured

/-! One actual initializer, fused primitive loop and terminal materializer
return their preceding data, trace and source charge together. No separate old
work producer is replayed at these selected boundaries. Component/native price
and complete working-space joins remain separate. The downstream placement
avoids the legacy seed-law import cycle. -/
namespace Blotto.BinaryReflectedNativeFused
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryPRGHeapResourceSource (capStore count)
open BinaryPRGHeapResourceLoop (Finished)
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable {n : ℕ}

def source (seed : BinarySeedLookupTree.Store) (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j))
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    ((FixedBinaryWord (capStore capacity).width × BinaryPRGHeapResourceLoop.Result seed (capStore capacity) n (count capacity)) × Trace) × ℕ :=
  let initialized := BinaryReflectedInitialFused.initial capacity resource hC hR
  let prepared := initialized.1
  let capWord : FixedBinaryWord (capStore capacity).width := ⟨prepared.1.1.ruler,prepared.1.1.size⟩
  let completed := BinaryHeapLoopPrimitiveMeasured.run seed prepared.1.1
    (BinaryPRGWordControllerBooleanResourceSource.capacityCanonical capacity hC) prepared.1.2 pc hp
  (((capWord,completed.1.1),wrap 32 2 [prepared.2,completed.1.2]),
    initialized.2 + completed.2 + 3)


theorem source_previous (seed : BinarySeedLookupTree.Store) (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j))
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    source seed capacity resource hC hR pc hp =
      BinaryPRGHeapNativeLifetime.sourceWithTraceAndWork seed capacity resource hC hR pc hp := by
  simp only [source,BinaryReflectedInitialFused.initial_record,BinaryPRGHeapNativeLifetime.sourceWithTraceAndWork,BinaryHeapLoopPrimitiveMeasured.run_eq_reference]

theorem source_cap (seed : BinarySeedLookupTree.Store) (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j))
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (source seed capacity resource hC hR pc hp).1.1.1 = (capStore capacity).cap := by
  rw [source_previous]
  exact BinaryPRGHeapNativeLifetime.sourceWithTrace_cap seed capacity resource hC hR pc hp

def native (seed : BinarySeedLookupTree.Store)
    (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j))
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (BinaryPRGWordControllerResource.Result seed capacity × Trace) × ℕ :=
  let drawn := source seed capacity resource hC hR pc hp
  match drawn.1.1.2.1 with
  | none => (((none,drawn.1.1.2.2),wrap 16 2 [drawn.1.2]),drawn.2 + 2)
  | some state =>
      let terminal := BinaryHeapMaterializationMeasured.materialize capacity
        (BinaryPRGWordControllerBooleanResourceSource.capacityTable capacity)
        drawn.1.1.1 (source_cap seed capacity resource hC hR pc hp) state
      (((some terminal.1.1,drawn.1.1.2.2),wrap 24 2 [drawn.1.2,terminal.1.2]),
        drawn.2 + terminal.2 + 4)


theorem native_previous (seed : BinarySeedLookupTree.Store) (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j))
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    native seed capacity resource hC hR pc hp =
      BinaryPRGHeapNativeLifetime.nativeWithTraceAndWork seed capacity resource hC hR pc hp := by
  simp only [native,source_previous,BinaryPRGHeapNativeLifetime.nativeWithTraceAndWork]
  split
  · rename_i hNone
    simp only [hNone]
  · rename_i state hSome
    simp only [hSome,BinaryHeapMaterializationMeasured.materialize_erases,
      BinaryHeapMaterializationMeasured.materialize_work]

end Blotto.BinaryReflectedNativeFused
