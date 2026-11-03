import Blotto.BinaryPRGHeapCallerLifetimePolynomial

/-! The actual traced seed store feeds the physical request and terminal
cache. Store, resource history and cache all remain retained. Only the input
seed list and the prepared request/caller roots are borrowed at entry. -/
namespace Blotto.BinaryPRGHeapSeededPrefixLifetime
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
set_option maxHeartbeats 2000000

structure Retained {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool) (seed : List Bool) where
  store : BinarySeedLookupTree.Store
  correct : store = BinarySeedLookupTree.prepare seed
  output : Option (BinaryPRGHeapCachedPrefixLifetime.CachedResult request rich) × FixedBinaryWord store.width

def erase {n : ℕ} {request : BinaryPRGRequest.Request n} {rich : Bool} {seed : List Bool}
    (result : Retained request rich seed) :
    Option (BinaryPRGHeapCachedPrefixLifetime.CachedResult request rich) × FixedBinaryWord (BinarySeedLookupTree.prepare seed).width :=
  result.correct ▸ result.output

def runWithTrace {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool) (seed : List Bool) :
    Retained request rich seed × Trace :=
  let prepared := BinaryWordStoreLifetime.prepareWithTrace seed
  let cached := BinaryPRGHeapCachedPrefixLifetime.runWithTrace prepared.1 request rich
  (⟨prepared.1,BinaryWordStoreLifetime.prepareWithTrace_erases seed,cached.1⟩,wrap 32 2 [prepared.2,cached.2])

theorem output_transport {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool)
    (first second : BinarySeedLookupTree.Store) (h : first = second) :
    (h ▸ (BinaryPRGHeapCachedPrefixLifetime.runWithTrace first request rich).1) =
      BinaryPRGHeapCachedPrefixLifetime.reference second request rich := by
  cases h
  exact BinaryPRGHeapCachedPrefixLifetime.runWithTrace_erasure first request rich

theorem runWithTrace_erasure {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool) (seed : List Bool) :
    erase (runWithTrace request rich seed).1 =
      BinaryPRGHeapCachedPrefixLifetime.reference (BinarySeedLookupTree.prepare seed) request rich :=
  output_transport request rich _ _ _

theorem seed_store_retained {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool) (seed : List Bool) :
    (runWithTrace request rich seed).1.store = (BinaryWordStoreLifetime.prepareWithTrace seed).1 := rfl

theorem uniform_usage : ∃ C d : ℕ,∀ {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool) (seed : List Bool),
    usage (runWithTrace request rich seed).2 ≤ C * (n + request.source.originalInputWordWidth + seed.length + 2)^d := by
  rcases BinaryPRGHeapCallerLifetimePolynomial.uniform_cached_usage with ⟨C,d,hBound⟩
  refine ⟨C * 2^d + 128,d + 1,?_⟩
  intro n request rich seed
  let prepared := BinaryWordStoreLifetime.prepareWithTrace seed
  have hE : prepared.1 = BinarySeedLookupTree.prepare seed := BinaryWordStoreLifetime.prepareWithTrace_erases seed
  have hW : prepared.1.width ≤ seed.length + 1 := by
    rw [hE]
    have h := BinarySeedLookupTree.prepare_width_bound seed
    have hLog := Nat.log2_le_self seed.length
    unfold binaryWordWidth at h
    omega
  have hCap : prepared.1.cap.value = seed.length := by rw [hE,BinarySeedLookupTree.prepare_cap]
  have hP := BinaryWordStoreLifetime.prepareWithTrace_bounds seed
  have hLog : binaryWordWidth seed.length ≤ seed.length + 1 := by
    have h := Nat.log2_le_self seed.length
    unfold binaryWordWidth
    omega
  have hPrep : usage prepared.2 ≤ 49 * seed.length + 33 := by
    change listCells prepared.2 + arraySlots prepared.2 ≤ _ ∧ framePeak prepared.2 ≤ _ at hP
    unfold usage BinaryPRGHeapPrimitiveLifetime.cells
    omega
  let X := n + request.source.originalInputWordWidth + seed.length + 2
  have hSource := hBound prepared.1 request rich
  have hSize : n + request.source.originalInputWordWidth + prepared.1.width + prepared.1.cap.value + 2 ≤ 2 * X := by
    dsimp only [X]
    omega
  have hp := Nat.mul_le_mul_left C (Nat.pow_le_pow_left hSize d)
  rw [Nat.mul_pow] at hp
  have hSmall : X^d ≤ X^(d + 1) := Nat.pow_le_pow_right (by dsimp [X]; omega) (by omega)
  have hLarge : X ≤ X^(d + 1) := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by dsimp [X]; omega : 0 < X) (show 1 ≤ d + 1 by omega)
  have hw := wrap_usage 32 2 [prepared.2,(BinaryPRGHeapCachedPrefixLifetime.runWithTrace prepared.1 request rich).2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change usage (wrap 32 2 [prepared.2,(BinaryPRGHeapCachedPrefixLifetime.runWithTrace prepared.1 request rich).2]) ≤ _
  change usage (BinaryPRGHeapCachedPrefixLifetime.runWithTrace prepared.1 request rich).2 ≤ _ at hSource
  change _ ≤ (C * 2^d + 128) * X^(d + 1)
  have hLength : seed.length ≤ X := by dsimp only [X]; omega
  have hOne : 1 ≤ X^(d + 1) := by omega
  have hScale := Nat.mul_le_mul_left (C * 2^d) hSmall
  have hLinear := Nat.mul_le_mul_left 49 (hLength.trans hLarge)
  nlinarith

theorem uniform_all_prefix : ∃ C d : ℕ,∀ {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool) (seed : List Bool)
    (borrowedRequestCells steps : ℕ),
    retainedHeap (borrowedRequestCells + seed.length) (runWithTrace request rich seed).2 steps ≤
        borrowedRequestCells + seed.length + C * (n + request.source.originalInputWordWidth + seed.length + 2)^d ∧
      framePeak ((runWithTrace request rich seed).2.take steps) ≤ C * (n + request.source.originalInputWordWidth + seed.length + 2)^d := by
  rcases uniform_usage with ⟨C,d,hBound⟩
  exact ⟨C,d,fun request rich seed borrowed steps => BinaryPRGHeapTraceUsage.all_prefix _ _ (hBound request rich seed) (borrowed + seed.length) steps⟩

end Blotto.BinaryPRGHeapSeededPrefixLifetime
