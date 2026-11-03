import Blotto.BinaryPRGHeapInitialLifetimeBound
import Blotto.BinaryPRGHeapMaterializationLifetime
import Blotto.BinaryPRGHeapLifetimePolynomial
import Blotto.BinaryPRGHeapResourceAt
import Blotto.BinaryPRGHeapLoopMeasuredWork

/-! Complete physical original-array resource allocation observer, from
initialization through the loop and native state materialization at the
incoming absolute seed cursor. Previous resource producers are proof views. -/

namespace Blotto.BinaryPRGHeapNativeLifetime
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGHeapTraceUsage
open BinaryPRGHeapResourceSource (capStore count)
open BinaryPRGHeapResourceLoop (Finished)
set_option maxHeartbeats 1500000

variable {n : ℕ}

def sourceWithTraceAndWork (seed : BinarySeedLookupTree.Store) (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j))
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    ((FixedBinaryWord (capStore capacity).width × BinaryPRGHeapResourceLoop.Result seed (capStore capacity) n (count capacity)) × Trace) × ℕ :=
  let prepared := BinaryPRGHeapInitialLifetime.initialWithTrace capacity resource hC hR
  let capWord : FixedBinaryWord (capStore capacity).width := ⟨prepared.1.1.ruler,prepared.1.1.size⟩
  let completed := BinaryPRGHeapLoopMeasuredWork.runWithTraceAndWork seed prepared.1.1
    (BinaryPRGWordControllerBooleanResourceSource.capacityCanonical capacity hC) prepared.1.2 pc hp
  (((capWord,completed.1.1),wrap 32 2 [prepared.2,completed.1.2]),
    (BinaryPRGHeapResourceSource.initialWithWork capacity resource hC hR).2 + completed.2 + 3)

def sourceWithTrace (seed : BinarySeedLookupTree.Store) (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j))
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (FixedBinaryWord (capStore capacity).width × BinaryPRGHeapResourceLoop.Result seed (capStore capacity) n (count capacity)) × Trace :=
  (sourceWithTraceAndWork seed capacity resource hC hR pc hp).1

theorem sourceWithTraceAndWork_charge (seed : BinarySeedLookupTree.Store)
    (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j))
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (sourceWithTraceAndWork seed capacity resource hC hR pc hp).2 =
      (BinaryPRGHeapResourceAt.sourceAt seed capacity resource hC hR pc hp).2 := by
  unfold sourceWithTraceAndWork BinaryPRGHeapResourceAt.sourceAt
  dsimp only
  simp only [BinaryPRGHeapInitialLifetime.initialWithTrace_erasure,
    BinaryPRGHeapLoopMeasuredWork.runWithTraceAndWork_charge]

theorem sourceWithTraceAndWork_bound (seed : BinarySeedLookupTree.Store)
    (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j))
    (D : ℕ) (hD : 0 < D)
    (hLattice : ∀ j,OnRationalLattice D (value (capacity.read j)))
    (hBox : ∀ j,0 ≤ value (capacity.read j) ∧ value (capacity.read j) ≤ 1)
    (hResourceLattice : ∀ j,OnRationalLattice D (value (resource.read j)))
    (hResourceBox : ∀ j,0 ≤ value (resource.read j) ∧
      value (resource.read j) ≤ value (capacity.read j))
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (sourceWithTraceAndWork seed capacity resource hC hR pc hp).2 ≤
      BinaryPRGHeapResourceSource.initialWorkEnvelope capacity resource +
        BinaryPRGHeapResourceSourceReservation.loopBound seed capacity resource hC hR D + 3 := by
  let prepared := BinaryPRGHeapResourceSource.initialWithWork capacity resource hC hR
  have hs := BinaryPRGHeapResourceInvariant.initial_lattice
    capacity resource hC hR D hResourceLattice hResourceBox
  have hl : ∀ j,OnRationalLattice D
      (value ((BinaryPRGWordControllerBooleanResourceUpdate.table
        (capStore capacity).cap (capStore capacity).tree n (count capacity)).read j)) := by
    rw [BinaryPRGWordControllerBooleanResourceSource.capacityTable]
    exact hLattice
  have hb : ∀ j,0 ≤ value ((BinaryPRGWordControllerBooleanResourceUpdate.table
        (capStore capacity).cap (capStore capacity).tree n (count capacity)).read j) ∧
      value ((BinaryPRGWordControllerBooleanResourceUpdate.table
        (capStore capacity).cap (capStore capacity).tree n (count capacity)).read j) ≤ 1 := by
    rw [BinaryPRGWordControllerBooleanResourceSource.capacityTable]
    exact hBox
  have hLoop := BinaryPRGHeapResourceReservation.runWithWork_source_bound
    (hC := BinaryPRGWordControllerBooleanResourceSource.capacityCanonical capacity hC)
    D hD hl hb seed prepared.1.1 prepared.1.2 hs pc hp
  have hInitial := BinaryPRGHeapResourceSource.initialWithWork_bound capacity resource hC hR
  change (BinaryPRGHeapResourceLoop.runWithWork seed prepared.1.1
    (BinaryPRGWordControllerBooleanResourceSource.capacityCanonical capacity hC)
    prepared.1.2 pc hp).2 ≤
      BinaryPRGHeapResourceSourceReservation.loopBound seed capacity resource hC hR D at hLoop
  change prepared.2 ≤ BinaryPRGHeapResourceSource.initialWorkEnvelope capacity resource at hInitial
  rw [sourceWithTraceAndWork_charge]
  unfold BinaryPRGHeapResourceAt.sourceAt
  dsimp only
  change prepared.2 + (BinaryPRGHeapResourceLoop.runWithWork seed prepared.1.1
    (BinaryPRGWordControllerBooleanResourceSource.capacityCanonical capacity hC)
    prepared.1.2 pc hp).2 + 3 ≤ _
  omega

theorem sourceWithTrace_erasure (seed : BinarySeedLookupTree.Store) (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j))
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (sourceWithTrace seed capacity resource hC hR pc hp).1 =
      (BinaryPRGHeapResourceAt.sourceAt seed capacity resource hC hR pc hp).1 := by
  unfold sourceWithTrace sourceWithTraceAndWork BinaryPRGHeapResourceAt.sourceAt
  dsimp only
  simp only [BinaryPRGHeapInitialLifetime.initialWithTrace_erasure,
    BinaryPRGHeapLoopMeasuredWork.runWithTraceAndWork_erases,
    BinaryPRGHeapLoopLifetime.runWithTrace_erasure]

theorem sourceWithTrace_cap (seed : BinarySeedLookupTree.Store) (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j))
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (sourceWithTrace seed capacity resource hC hR pc hp).1.1 = (capStore capacity).cap := by
  rw [sourceWithTrace_erasure]
  exact BinaryPRGHeapResourceAt.sourceAt_cap seed capacity resource hC hR pc hp

def nativeWithTrace (seed : BinarySeedLookupTree.Store) (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j))
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    BinaryPRGWordControllerResource.Result seed capacity × Trace :=
  let drawn := sourceWithTrace seed capacity resource hC hR pc hp
  match drawn.1.2.1 with
  | none => ((none,drawn.1.2.2),wrap 16 2 [drawn.2])
  | some state =>
      let terminal := BinaryPRGHeapMaterializationLifetime.materializeWithTrace capacity
        (BinaryPRGWordControllerBooleanResourceSource.capacityTable capacity)
        drawn.1.1 (sourceWithTrace_cap seed capacity resource hC hR pc hp) state
      ((some terminal.1,drawn.1.2.2),wrap 24 2 [drawn.2,terminal.2])

def nativeWithTraceAndWork (seed : BinarySeedLookupTree.Store)
    (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j))
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (BinaryPRGWordControllerResource.Result seed capacity × Trace) × ℕ :=
  let drawn := sourceWithTraceAndWork seed capacity resource hC hR pc hp
  match drawn.1.1.2.1 with
  | none => (((none,drawn.1.1.2.2),wrap 16 2 [drawn.1.2]),drawn.2 + 2)
  | some state =>
      let terminal := BinaryPRGHeapMaterializationLifetime.materializeWithTrace capacity
        (BinaryPRGWordControllerBooleanResourceSource.capacityTable capacity)
        drawn.1.1.1 (sourceWithTrace_cap seed capacity resource hC hR pc hp) state
      let terminalCharge := (BinaryPRGHeapResourceMaterialization.materializeWithWork capacity
        (BinaryPRGWordControllerBooleanResourceSource.capacityTable capacity)
        drawn.1.1.1 (sourceWithTrace_cap seed capacity resource hC hR pc hp) state).2
      (((some terminal.1,drawn.1.1.2.2),wrap 24 2 [drawn.1.2,terminal.2]),
        drawn.2 + terminalCharge + 4)

theorem nativeWithTraceAndWork_erases (seed : BinarySeedLookupTree.Store)
    (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j))
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (nativeWithTraceAndWork seed capacity resource hC hR pc hp).1 =
      nativeWithTrace seed capacity resource hC hR pc hp := by
  unfold nativeWithTraceAndWork nativeWithTrace sourceWithTrace
  dsimp only
  cases (sourceWithTraceAndWork seed capacity resource hC hR pc hp).1.1.2.1 <;> rfl

theorem nativeWithTraceAndWork_charge (seed : BinarySeedLookupTree.Store)
    (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j))
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (nativeWithTraceAndWork seed capacity resource hC hR pc hp).2 =
      (BinaryPRGHeapResourceAt.nativeAt seed capacity resource hC hR pc hp).2 := by
  have hSource := sourceWithTrace_erasure seed capacity resource hC hR pc hp
  have hCharge := sourceWithTraceAndWork_charge seed capacity resource hC hR pc hp
  unfold nativeWithTraceAndWork BinaryPRGHeapResourceAt.nativeAt
  dsimp only
  simp only [← hSource, sourceWithTrace]
  cases hResult : (sourceWithTraceAndWork seed capacity resource hC hR pc hp).1.1.2.1
  · simpa only [hResult] using congrArg (fun x => x + 2) hCharge
  · simpa only [hResult] using congrArg (fun x => x +
      (BinaryPRGHeapResourceMaterialization.materializeWithWork capacity
        (BinaryPRGWordControllerBooleanResourceSource.capacityTable capacity)
        (sourceWithTraceAndWork seed capacity resource hC hR pc hp).1.1.1
        (sourceWithTrace_cap seed capacity resource hC hR pc hp) _).2 + 4) hCharge

theorem nativeWithTraceAndWork_bound (seed : BinarySeedLookupTree.Store)
    (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j))
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value)
    (I M H : ℕ)
    (hInitial : (BinaryPRGHeapResourceSource.initialWithWork capacity resource hC hR).2 ≤ I)
    (hLoop : (BinaryPRGHeapLoopMeasuredWork.runWithTraceAndWork seed
      (BinaryPRGHeapResourceSource.initialWithWork capacity resource hC hR).1.1
      (BinaryPRGWordControllerBooleanResourceSource.capacityCanonical capacity hC)
      (BinaryPRGHeapResourceSource.initialWithWork capacity resource hC hR).1.2 pc hp).2 ≤ M)
    (hHeap : ∀ state : Finished (capStore capacity) n (count capacity),
      (sourceWithTrace seed capacity resource hC hR pc hp).1.2.1 = some state →
        state.heap.tape.length ≤ H) :
    (nativeWithTraceAndWork seed capacity resource hC hR pc hp).2 ≤ I + M +
      BinaryPRGHeapResourceSourceReservation.terminalBound n (capStore capacity).width H + 7 := by
  rw [nativeWithTraceAndWork_charge]
  apply BinaryPRGHeapResourceAt.nativeAt_bound seed capacity resource hC hR pc hp
    I M H hInitial
  · simpa only [BinaryPRGHeapLoopMeasuredWork.runWithTraceAndWork_charge] using hLoop
  · intro state hSome
    apply hHeap state
    rw [sourceWithTrace_erasure]
    exact hSome

theorem nativeWithTrace_erasure (seed : BinarySeedLookupTree.Store) (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j))
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (nativeWithTrace seed capacity resource hC hR pc hp).1 =
      (BinaryPRGHeapResourceAt.nativeAt seed capacity resource hC hR pc hp).1 := by
  unfold nativeWithTrace BinaryPRGHeapResourceAt.nativeAt
  dsimp only
  simp only [sourceWithTrace_erasure]
  cases (BinaryPRGHeapResourceAt.sourceAt seed capacity resource hC hR pc hp).1.2.1
  <;> simp only [BinaryPRGHeapMaterializationLifetime.materializeWithTrace_erasure]

theorem sourceWithTrace_usage (seed : BinarySeedLookupTree.Store) (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j))
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) (I L : ℕ)
    (hI : usage (BinaryPRGHeapInitialLifetime.initialWithTrace capacity resource hC hR).2 ≤ I)
    (hL : let prepared := BinaryPRGHeapInitialLifetime.initialWithTrace capacity resource hC hR
      usage (BinaryPRGHeapLoopLifetime.runWithTrace seed prepared.1.1
        (BinaryPRGWordControllerBooleanResourceSource.capacityCanonical capacity hC) prepared.1.2 pc hp).2 ≤ L) :
    usage (sourceWithTrace seed capacity resource hC hR pc hp).2 ≤ I + L + 38 := by
  let prepared := BinaryPRGHeapInitialLifetime.initialWithTrace capacity resource hC hR
  let completed := BinaryPRGHeapLoopLifetime.runWithTrace seed prepared.1.1
    (BinaryPRGWordControllerBooleanResourceSource.capacityCanonical capacity hC) prepared.1.2 pc hp
  have hw := wrap_usage 32 2 [prepared.2,completed.2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change usage (wrap 32 2 [prepared.2,completed.2]) ≤ _
  change usage prepared.2 ≤ I at hI
  change usage completed.2 ≤ L at hL
  omega

theorem nativeWithTrace_usage (seed : BinarySeedLookupTree.Store) (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j))
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) (I L H : ℕ)
    (hI : usage (BinaryPRGHeapInitialLifetime.initialWithTrace capacity resource hC hR).2 ≤ I)
    (hL : let prepared := BinaryPRGHeapInitialLifetime.initialWithTrace capacity resource hC hR
      usage (BinaryPRGHeapLoopLifetime.runWithTrace seed prepared.1.1
        (BinaryPRGWordControllerBooleanResourceSource.capacityCanonical capacity hC) prepared.1.2 pc hp).2 ≤ L)
    (hHeap : ∀ state : Finished (capStore capacity) n (count capacity),
      (sourceWithTrace seed capacity resource hC hR pc hp).1.2.1 = some state → state.heap.tape.length ≤ H) :
    usage (nativeWithTrace seed capacity resource hC hR pc hp).2 ≤ I + L +
      BinaryPRGHeapMaterializationLifetime.envelope n H (capStore capacity).width + 100 := by
  have hSource := sourceWithTrace_usage seed capacity resource hC hR pc hp I L hI hL
  unfold nativeWithTrace
  dsimp only
  cases hResult : (sourceWithTrace seed capacity resource hC hR pc hp).1.2.1 with
  | none =>
      have hw := wrap_usage 16 2 [(sourceWithTrace seed capacity resource hC hR pc hp).2]
      simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
      dsimp only
      omega
  | some state =>
      have ht := BinaryPRGHeapMaterializationLifetime.materializeWithTrace_usage capacity
        (BinaryPRGWordControllerBooleanResourceSource.capacityTable capacity)
        (sourceWithTrace seed capacity resource hC hR pc hp).1.1
        (sourceWithTrace_cap seed capacity resource hC hR pc hp) state H (hHeap state hResult)
      change _ ≤ BinaryPRGHeapMaterializationLifetime.envelope n H (capStore capacity).width at ht
      have hw := wrap_usage 24 2 [(sourceWithTrace seed capacity resource hC hR pc hp).2,
        (BinaryPRGHeapMaterializationLifetime.materializeWithTrace capacity
          (BinaryPRGWordControllerBooleanResourceSource.capacityTable capacity)
          (sourceWithTrace seed capacity resource hC hR pc hp).1.1
          (sourceWithTrace_cap seed capacity resource hC hR pc hp) state).2]
      simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
      dsimp only
      omega

end Blotto.BinaryPRGHeapNativeLifetime
