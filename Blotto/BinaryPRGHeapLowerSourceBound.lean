import Blotto.BinaryPRGHeapLowerSourceLifetime
import Blotto.BinaryPRGHeapThreeNativeLifetimeBound
import Blotto.BinaryPRGHeapNativeLifetimePolynomial

/-! Original three-array heights derive initialization, lower-loop, returned
heap and native materialization reservations. No reached width, heap cap or
primitive price is supplied by the caller. -/
namespace Blotto.BinaryPRGHeapLowerSourceBound
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGHeapTraceUsage BinaryPRGHeapLowerSourceLifetime
open BinaryPRGHeapResourceSource (capStore count)
open BinaryPRGHeapResourceThreeSource (inputWidth initialCells heapCap)
set_option maxHeartbeats 2000000

theorem initial_bounds (s : ℕ) (capacity resource : FixedArrayTable 3 SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j))
    (hCapacity : ∀ j,RationalHeight (value (capacity.read j)) s)
    (hResource : ∀ j,RationalHeight (value (resource.read j)) s) :
    let prepared := BinaryPRGHeapInitialLifetime.initialWithTrace capacity resource hC hR
    prepared.1.1.heap.tape.length ≤ initialCells s ∧ prepared.1.2.heap.tape.length ≤ initialCells s ∧
      BinaryPRGHeapResourceThreeStep.HeightInv 2 s prepared.1.2 := by
  obtain ⟨hc,hr⟩ := BinaryPRGHeapThreeNativeLifetimeBound.input_widths s capacity resource hC hR hCapacity hResource
  have hW : 1 ≤ inputWidth s := by unfold inputWidth BinaryPRGWordControllerBooleanResourceThreeWork.widthBound; omega
  have hHeaps := BinaryPRGHeapResourceInputBounds.initial_heaps_bound capacity resource hC hR (inputWidth s) hW hc hr
  dsimp only
  rw [BinaryPRGHeapInitialLifetime.initialWithTrace_erasure]
  refine ⟨hHeaps.1,hHeaps.2,?_⟩
  unfold BinaryPRGHeapResourceThreeStep.HeightInv
  rw [BinaryPRGHeapResourceSource.initialWithWork_reference]
  exact BinaryPRGWordControllerBooleanResourceThreeWork.source_initial_height capacity resource hC hR s hResource

theorem loop_usage (s : ℕ) (hs : 2 ≤ s) (capacity resource : FixedArrayTable 3 SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j))
    (hCapacity : ∀ j,RationalHeight (value (capacity.read j)) s)
    (hResource : ∀ j,RationalHeight (value (resource.read j)) s) :
    let prepared := BinaryPRGHeapInitialLifetime.initialWithTrace capacity resource hC hR
    usage (BinaryPRGHeapLowerLifetime.runWithTrace prepared.1.1
      (BinaryPRGWordControllerBooleanResourceSource.capacityCanonical capacity hC) prepared.1.2).2 ≤
      BinaryPRGHeapLifetimePolynomial.threeLoopEnvelope s 0 0 := by
  let prepared := BinaryPRGHeapInitialLifetime.initialWithTrace capacity resource hC hR
  have hInitial := initial_bounds s capacity resource hC hR hCapacity hResource
  change prepared.1.1.heap.tape.length ≤ _ ∧ prepared.1.2.heap.tape.length ≤ _ ∧ _ at hInitial
  have hCap : ∀ j,RationalHeight (value ((BinaryPRGWordControllerBooleanResourceUpdate.table
      (capStore capacity).cap (capStore capacity).tree 3 (count capacity)).read j)) s := by
    rw [BinaryPRGWordControllerBooleanResourceSource.capacityTable]
    exact hCapacity
  have h := BinaryPRGHeapLowerLifetimeBound.height_usage
    (hC := BinaryPRGWordControllerBooleanResourceSource.capacityCanonical capacity hC)
    2 s hs hCap prepared.1.1 prepared.1.2 hInitial.2.2
  exact h.trans (BinaryPRGHeapLifetimePolynomial.sourceEnvelope_mono le_rfl hInitial.2.1 hInitial.1
    (BinaryPRGHeapResourceInputBounds.source_depth capacity) le_rfl le_rfl le_rfl le_rfl)

theorem returned_heap (s : ℕ) (hs : 2 ≤ s) (capacity resource : FixedArrayTable 3 SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j))
    (hCapacity : ∀ j,RationalHeight (value (capacity.read j)) s)
    (hResource : ∀ j,RationalHeight (value (resource.read j)) s) :
    (sourceWithTrace capacity resource hC hR).1.2.heap.tape.length ≤ heapCap s := by
  let prepared := BinaryPRGHeapInitialLifetime.initialWithTrace capacity resource hC hR
  have hInitial := initial_bounds s capacity resource hC hR hCapacity hResource
  change prepared.1.1.heap.tape.length ≤ _ ∧ prepared.1.2.heap.tape.length ≤ _ ∧ _ at hInitial
  have hCap : ∀ j,RationalHeight (value ((BinaryPRGWordControllerBooleanResourceUpdate.table
      (capStore capacity).cap (capStore capacity).tree 3 (count capacity)).read j)) s := by
    rw [BinaryPRGWordControllerBooleanResourceSource.capacityTable]
    exact hCapacity
  have h := BinaryPRGHeapLowerLifetimeBound.height_returned
    (hC := BinaryPRGWordControllerBooleanResourceSource.capacityCanonical capacity hC)
    2 s hs hCap prepared.1.1 prepared.1.2 hInitial.2.2
  have hMono : BinaryPRGHeapResourceReservation.sourceHeapCap prepared.1.2.heap.tape.length 3
      (capStore capacity).width (inputWidth s) ≤ heapCap s := by
    unfold heapCap BinaryPRGHeapResourceReservation.sourceHeapCap
      BinaryPRGHeapResourceReservation.sourceSize BinaryPRGWordStoreHeap.heapBound
    have hd := BinaryPRGHeapResourceInputBounds.source_depth capacity
    gcongr
    exact hInitial.2.1
  exact h.2.trans hMono

def envelope (s : ℕ) : ℕ :=
  BinaryPRGHeapInitialLifetimeBound.envelope 3 (inputWidth s) (binaryWordWidth 3) +
    BinaryPRGHeapLifetimePolynomial.threeLoopEnvelope s 0 0 +
    BinaryPRGHeapMaterializationLifetime.envelope 3 (heapCap s) (binaryWordWidth 3)+100

theorem nativeWithTrace_usage (s : ℕ) (hs : 2 ≤ s) (capacity resource : FixedArrayTable 3 SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j))
    (hCapacity : ∀ j,RationalHeight (value (capacity.read j)) s)
    (hResource : ∀ j,RationalHeight (value (resource.read j)) s) :
    usage (nativeWithTrace capacity resource hC hR).2 ≤ envelope s := by
  obtain ⟨hc,hr⟩ := BinaryPRGHeapThreeNativeLifetimeBound.input_widths s capacity resource hC hR hCapacity hResource
  have hW : 1 ≤ inputWidth s := by unfold inputWidth BinaryPRGWordControllerBooleanResourceThreeWork.widthBound; omega
  have hInitial := BinaryPRGHeapInitialLifetimeBound.initialWithTrace_usage capacity resource hC hR _ hW hc hr
  have hLoop := loop_usage s hs capacity resource hC hR hCapacity hResource
  have h := BinaryPRGHeapLowerSourceLifetime.nativeWithTrace_usage capacity resource hC hR _ _ _ hInitial hLoop
    (returned_heap s hs capacity resource hC hR hCapacity hResource)
  have hm := BinaryPRGHeapNativeLifetimeBound.materialization_depth_mono 3 (heapCap s)
    (BinaryPRGHeapResourceInputBounds.source_depth capacity)
  unfold envelope
  omega

theorem all_prefix (s : ℕ) (hs : 2 ≤ s) (capacity resource : FixedArrayTable 3 SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j))
    (hCapacity : ∀ j,RationalHeight (value (capacity.read j)) s)
    (hResource : ∀ j,RationalHeight (value (resource.read j)) s) (borrowed steps : ℕ) :
    retainedHeap borrowed (nativeWithTrace capacity resource hC hR).2 steps ≤ borrowed + envelope s ∧
      framePeak ((nativeWithTrace capacity resource hC hR).2.take steps) ≤ envelope s :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (nativeWithTrace_usage s hs capacity resource hC hR hCapacity hResource) borrowed steps

theorem envelope_polynomial : ∃ C d : ℕ,∀ s,envelope s ≤ C*(s+2)^d := by
  rcases BinaryPRGHeapNativeLifetimePolynomial.three_envelope_polynomial with ⟨C,d,hBound⟩
  refine ⟨C,d,?_⟩
  intro s
  have h := hBound ⟨0,s,0,0,0⟩
  have hSize : BinaryPRGHeapResourcePolynomial.inputSize ⟨0,s,0,0,0⟩+1 = s+2 := by
    simp [BinaryPRGHeapResourcePolynomial.inputSize,binaryWordWidth]
  rw [hSize] at h
  exact h

theorem uniform_native_usage : ∃ C d : ℕ,∀ (s : ℕ),2 ≤ s →
    ∀ (capacity resource : FixedArrayTable 3 SignedWord)
      (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j)),
    (∀ j,RationalHeight (value (capacity.read j)) s) → (∀ j,RationalHeight (value (resource.read j)) s) →
    usage (nativeWithTrace capacity resource hC hR).2 ≤ C*(s+2)^d := by
  rcases envelope_polynomial with ⟨C,d,hBound⟩
  exact ⟨C,d,fun s hs capacity resource hC hR hCapacity hResource =>
    (nativeWithTrace_usage s hs capacity resource hC hR hCapacity hResource).trans (hBound s)⟩

end Blotto.BinaryPRGHeapLowerSourceBound
