import Blotto.BinaryPRGHeapRequestLifetime
import Blotto.BinaryTerminalCacheLifetime

/-! The actual physical request state feeds the traced terminal cache. The
capacity/resource tapes, materialized state and all cache regions stay live;
the seed and prepared request are borrowed from the enclosing caller. -/
namespace Blotto.BinaryPRGHeapCachedPrefixLifetime
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage BinaryPRGResourceWork BinaryPRGTerminalWork
open BinaryTerminalCacheLifetime
set_option maxHeartbeats 1500000

def CachedResult {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool) :=
  Σ state : BinaryResourcePair.Certified (resourceInput request rich).length,CacheData (terminalInput request rich state)

def reference {n : ℕ} (seed : BinarySeedLookupTree.Store) (request : BinaryPRGRequest.Request n) (rich : Bool) :
    Option (CachedResult request rich) × FixedBinaryWord seed.width :=
  let resource := BinaryPRGWordControllerResource.requestRun seed request rich
  (resource.1.map (fun state => ⟨state,erase (BinaryCachedTerminalPreparation.prepare (terminalInput request rich state))⟩),resource.2)

def runWithTrace {n : ℕ} (seed : BinarySeedLookupTree.Store) (request : BinaryPRGRequest.Request n) (rich : Bool) :
    (Option (CachedResult request rich) × FixedBinaryWord seed.width) × Trace :=
  let resource := BinaryPRGHeapRequestLifetime.run seed request rich
  match resource.1.1 with
  | none => ((none,resource.1.2),wrap 16 2 [resource.2])
  | some state =>
      let cached := cacheWithTrace (terminalInput request rich state)
      ((some ⟨state,cached.1⟩,resource.1.2),wrap 24 2 [resource.2,cached.2])

theorem runWithTrace_erasure {n : ℕ} (seed : BinarySeedLookupTree.Store) (request : BinaryPRGRequest.Request n) (rich : Bool) :
    (runWithTrace seed request rich).1 = reference seed request rich := by
  unfold runWithTrace reference
  dsimp only
  rw [← BinaryPRGHeapRequestLifetime.run_erasure]
  cases (BinaryPRGHeapRequestLifetime.run seed request rich).1.1 <;>
    simp only [cacheWithTrace_erases] <;> rfl

noncomputable def envelope {n : ℕ} (request : BinaryPRGRequest.Request n) (indexWidth seedCap : ℕ) : ℕ :=
  BinaryPRGHeapRequestLifetime.envelope request indexWidth seedCap + 2 * indexWidth +
    BinaryTerminalCacheLifetime.envelope n request.source.originalInputWordWidth + 4 * n + 80

theorem runWithTrace_usage {n : ℕ} (seed : BinarySeedLookupTree.Store) (request : BinaryPRGRequest.Request n) (rich : Bool) :
    usage (runWithTrace seed request rich).2 ≤ envelope request seed.width seed.cap.value := by
  have hr := BinaryPRGHeapRequestLifetime.run_usage seed request rich
  unfold runWithTrace
  dsimp only
  cases hs : (BinaryPRGHeapRequestLifetime.run seed request rich).1.1 with
  | none =>
      have hw := wrap_usage 16 2 [(BinaryPRGHeapRequestLifetime.run seed request rich).2]
      simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
      dsimp only
      unfold envelope
      omega
  | some state =>
      have hNative : (BinaryPRGWordControllerResource.requestRun seed request rich).1 = some state := by
        rw [← BinaryPRGHeapRequestLifetime.run_erasure]
        exact hs
      have hOld : (resourceWork request rich seed.cap.value (BinaryWordIndexCoinController.reader seed)).1.1 = some state := by
        have h := congrArg Prod.fst (BinaryPRGWordControllerResource.requestRun_state seed request rich)
        exact h.symm.trans hNative
      have hc := reached_cache_bound request rich seed.cap.value (BinaryWordIndexCoinController.reader seed) state hOld
      rw [cacheBound_eq] at hc
      have hUsage : usage (cacheWithTrace (terminalInput request rich state)).2 ≤
          BinaryTerminalCacheLifetime.envelope n request.source.originalInputWordWidth + 4 * n + 18 := by
        unfold usage BinaryPRGHeapPrimitiveLifetime.cells
        omega
      have hw := wrap_usage 24 2 [(BinaryPRGHeapRequestLifetime.run seed request rich).2,
        (cacheWithTrace (terminalInput request rich state)).2]
      simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
      dsimp only
      unfold envelope
      omega

theorem all_prefix {n : ℕ} (seed : BinarySeedLookupTree.Store) (request : BinaryPRGRequest.Request n) (rich : Bool)
    (borrowed steps : ℕ) :
    retainedHeap borrowed (runWithTrace seed request rich).2 steps ≤ borrowed + envelope request seed.width seed.cap.value ∧
      framePeak ((runWithTrace seed request rich).2.take steps) ≤ envelope request seed.width seed.cap.value :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (runWithTrace_usage seed request rich) borrowed steps

end Blotto.BinaryPRGHeapCachedPrefixLifetime
