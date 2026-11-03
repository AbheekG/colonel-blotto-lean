import Blotto.BinaryPRGHeapNativeLifetimePolynomial
import Blotto.BinaryPRGHeapResourceRequest

/-! The actual prepared request selects retained arrays, then consumes the
complete physical native source observer. Request preparation and the seed
remain borrowed here; selection adds only its source record reservation. -/
namespace Blotto.BinaryPRGHeapRequestLifetime
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGResourceWork BinaryPRGHeapTraceUsage
set_option maxHeartbeats 1500000

variable {n : ℕ}

def runAtWithTraceAndWork (seed : BinarySeedLookupTree.Store)
    (request : BinaryPRGRequest.Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (BinaryPRGWordControllerResource.Result seed (resourceInput request rich).length × Trace) × ℕ :=
  let selected := resourceInput request rich
  let drawn := BinaryPRGHeapNativeLifetime.nativeWithTraceAndWork seed selected.length selected.resource
    (resource_canonical request rich).2.1 (resource_canonical request rich).2.2 pc hp
  ((drawn.1.1,wrap 24 2 [drawn.1.2]),drawn.2)

def runAt (seed : BinarySeedLookupTree.Store) (request : BinaryPRGRequest.Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    BinaryPRGWordControllerResource.Result seed (resourceInput request rich).length × Trace :=
  (runAtWithTraceAndWork seed request rich pc hp).1

theorem runAtWithTraceAndWork_charge (seed : BinarySeedLookupTree.Store)
    (request : BinaryPRGRequest.Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (runAtWithTraceAndWork seed request rich pc hp).2 =
      (BinaryPRGHeapResourceAt.nativeAt seed
        (resourceInput request rich).length (resourceInput request rich).resource
        (resource_canonical request rich).2.1 (resource_canonical request rich).2.2 pc hp).2 :=
  BinaryPRGHeapNativeLifetime.nativeWithTraceAndWork_charge _ _ _ _ _ _ _

theorem runAtWithTraceAndWork_zero_charge (seed : BinarySeedLookupTree.Store)
    (request : BinaryPRGRequest.Request n) (rich : Bool) :
    (runAtWithTraceAndWork seed request rich
      (BinaryWordIndexCoinController.zeroIndex seed)
      (by rw [BinaryWordIndexCoinController.zeroIndex_value]; omega)).2 =
      (BinaryPRGHeapResourceRequest.run seed request rich).2 := by
  rw [runAtWithTraceAndWork_charge]
  rfl

theorem runAt_selected (seed : BinarySeedLookupTree.Store)
    (request : BinaryPRGRequest.Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    runAt seed request rich pc hp =
      let drawn := BinaryPRGHeapNativeLifetime.nativeWithTrace seed
        (resourceInput request rich).length (resourceInput request rich).resource
        (resource_canonical request rich).2.1 (resource_canonical request rich).2.2 pc hp
      (drawn.1,wrap 24 2 [drawn.2]) := by
  unfold runAt runAtWithTraceAndWork
  simp only [BinaryPRGHeapNativeLifetime.nativeWithTraceAndWork_erases]

theorem runAt_erasure (seed : BinarySeedLookupTree.Store) (request : BinaryPRGRequest.Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (runAt seed request rich pc hp).1 = BinaryPRGWordControllerResource.run seed
      (resourceInput request rich).length (resource_canonical request rich).2.1
      (BinaryResourcePair.initial (resourceInput request rich).length (resourceInput request rich).resource
        (resource_canonical request rich).2.1 (resource_canonical request rich).2.2) pc hp := by
  rw [runAt_selected]
  exact (BinaryPRGHeapNativeLifetime.nativeWithTrace_erasure _ _ _ _ _ _ _).trans
    (BinaryPRGHeapResourceAt.nativeAt_erasure _ _ _ _ _ _ _)

noncomputable def envelope (request : BinaryPRGRequest.Request n) (indexWidth seedCap : ℕ) : ℕ :=
  BinaryPRGHeapNativeLifetimeBound.envelope n
    (BinaryPRGWordControllerBooleanResourceLoopWork.widthBound request.source.normalizedInput.latticeDenominator)
    request.source.normalizedInput.latticeDenominator indexWidth seedCap + 28

theorem runAt_usage (seed : BinarySeedLookupTree.Store) (request : BinaryPRGRequest.Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    usage (runAt seed request rich pc hp).2 ≤ envelope request seed.width seed.cap.value := by
  obtain ⟨hl,hr,hb,hrb⟩ := resource_lattice_boxes request rich
  obtain ⟨hcWidth,hrWidth⟩ := BinaryPRGHeapResourceRequest.input_widths request rich
  have h := BinaryPRGHeapNativeLifetimeBound.nativeWithTrace_input_usage seed
    (resourceInput request rich).length (resourceInput request rich).resource
    (resource_canonical request rich).2.1 (resource_canonical request rich).2.2 _ _
    (by unfold BinaryPRGWordControllerBooleanResourceLoopWork.widthBound; omega)
    request.source.normalizedInput.latticeDenominator_pos hcWidth hrWidth hl hb hr hrb pc hp
  have hw := wrap_usage 24 2 [(BinaryPRGHeapNativeLifetime.nativeWithTrace seed
    (resourceInput request rich).length (resourceInput request rich).resource
    (resource_canonical request rich).2.1 (resource_canonical request rich).2.2 pc hp).2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  rw [runAt_selected]
  exact hw.trans (by unfold envelope; omega)

theorem uniform_runAt_usage : ∃ C d : ℕ,
    ∀ {n : ℕ} (seed : BinarySeedLookupTree.Store) (request : BinaryPRGRequest.Request n) (rich : Bool)
      (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value),
    usage (runAt seed request rich pc hp).2 ≤
      C * (n + request.source.originalInputWordWidth + seed.width + seed.cap.value + 1)^d := by
  rcases BinaryPRGHeapNativeLifetimePolynomial.uniform_original_array_native_usage with ⟨C,d,hBound⟩
  refine ⟨C * 7^d + 28,d,?_⟩
  intro n seed request rich pc hp
  obtain ⟨hl,hr,hb,hrb⟩ := resource_lattice_boxes request rich
  obtain ⟨hcWidth,hrWidth⟩ := BinaryPRGHeapResourceRequest.input_widths request rich
  have h := hBound seed (resourceInput request rich).length (resourceInput request rich).resource
    (resource_canonical request rich).2.1 (resource_canonical request rich).2.2 _ _
    (by unfold BinaryPRGWordControllerBooleanResourceLoopWork.widthBound; omega)
    request.source.normalizedInput.latticeDenominator_pos hcWidth hrWidth hl hb hr hrb pc hp
  have hWidth := request.source.normalized_lattice_wordWidth_original
  have hSize : n + BinaryPRGWordControllerBooleanResourceLoopWork.widthBound
      request.source.normalizedInput.latticeDenominator +
      binaryWordWidth request.source.normalizedInput.latticeDenominator + seed.width + seed.cap.value + 1 ≤
      7 * (n + request.source.originalInputWordWidth + seed.width + seed.cap.value + 1) := by
    unfold BinaryPRGWordControllerBooleanResourceLoopWork.widthBound
    omega
  have hpw := Nat.mul_le_mul_left C (Nat.pow_le_pow_left hSize d)
  rw [Nat.mul_pow] at hpw
  have hOne := Nat.one_le_pow d (n + request.source.originalInputWordWidth + seed.width + seed.cap.value + 1) (by omega)
  have hw := wrap_usage 24 2 [(BinaryPRGHeapNativeLifetime.nativeWithTrace seed
    (resourceInput request rich).length (resourceInput request rich).resource
    (resource_canonical request rich).2.1 (resource_canonical request rich).2.2 pc hp).2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  rw [runAt_selected]
  nlinarith

def runWithTraceAndWork (seed : BinarySeedLookupTree.Store)
    (request : BinaryPRGRequest.Request n) (rich : Bool) :
    (BinaryPRGWordControllerResource.Result seed (resourceInput request rich).length × Trace) × ℕ :=
  let drawn := runAtWithTraceAndWork seed request rich (BinaryWordIndexCoinController.zeroIndex seed)
    (by rw [BinaryWordIndexCoinController.zeroIndex_value]; omega)
  ((drawn.1.1,wrapList seed.cap.bits.length 16 (seed.cap.bits.length + 2) [drawn.1.2]),
    drawn.2)

def run (seed : BinarySeedLookupTree.Store) (request : BinaryPRGRequest.Request n) (rich : Bool) :
    BinaryPRGWordControllerResource.Result seed (resourceInput request rich).length × Trace :=
  (runWithTraceAndWork seed request rich).1

theorem runWithTraceAndWork_charge (seed : BinarySeedLookupTree.Store)
    (request : BinaryPRGRequest.Request n) (rich : Bool) :
    (runWithTraceAndWork seed request rich).2 =
      (BinaryPRGHeapResourceRequest.run seed request rich).2 :=
  runAtWithTraceAndWork_zero_charge seed request rich

theorem run_selected (seed : BinarySeedLookupTree.Store)
    (request : BinaryPRGRequest.Request n) (rich : Bool) :
    run seed request rich =
      let drawn := runAt seed request rich (BinaryWordIndexCoinController.zeroIndex seed)
        (by rw [BinaryWordIndexCoinController.zeroIndex_value]; omega)
      (drawn.1,wrapList seed.cap.bits.length 16 (seed.cap.bits.length + 2) [drawn.2]) := by
  unfold run runWithTraceAndWork runAt
  rfl

theorem run_erasure (seed : BinarySeedLookupTree.Store) (request : BinaryPRGRequest.Request n) (rich : Bool) :
    (run seed request rich).1 = BinaryPRGWordControllerResource.requestRun seed request rich :=
  by rw [run_selected]; exact runAt_erasure seed request rich _ _

theorem run_usage (seed : BinarySeedLookupTree.Store) (request : BinaryPRGRequest.Request n) (rich : Bool) :
    usage (run seed request rich).2 ≤ envelope request seed.width seed.cap.value + 2 * seed.width + 20 := by
  have h := runAt_usage seed request rich (BinaryWordIndexCoinController.zeroIndex seed)
    (by rw [BinaryWordIndexCoinController.zeroIndex_value]; omega)
  have hw := wrapList_usage seed.cap.bits.length 16 (seed.cap.bits.length + 2)
    [(runAt seed request rich (BinaryWordIndexCoinController.zeroIndex seed)
      (by rw [BinaryWordIndexCoinController.zeroIndex_value]; omega)).2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,seed.cap.size] at hw
  rw [run_selected]
  simp only [seed.cap.size]
  omega

theorem all_prefix (seed : BinarySeedLookupTree.Store) (request : BinaryPRGRequest.Request n) (rich : Bool)
    (borrowed steps : ℕ) :
    retainedHeap borrowed (run seed request rich).2 steps ≤
        borrowed + envelope request seed.width seed.cap.value + 2 * seed.width + 20 ∧
      framePeak ((run seed request rich).2.take steps) ≤ envelope request seed.width seed.cap.value + 2 * seed.width + 20 := by
  have h := BinaryPRGHeapTraceUsage.all_prefix _ _ (run_usage seed request rich) borrowed steps
  simpa only [Nat.add_assoc] using h

end Blotto.BinaryPRGHeapRequestLifetime
