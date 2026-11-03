import Blotto.BinaryTerminalCacheLifetime
import Blotto.BinaryPRGWordControllerTerminal
import Blotto.BinaryPRGHeapTraceUsage

/-! Reattach erased correctness fields to the actual retained cache. The
former work annotation is zeroed, without running classification, packing,
route construction or pivot arithmetic a second time. -/
namespace Blotto.BinaryTerminalCacheCertificate
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage BinaryTerminalCacheLifetime
open BinaryCachedTerminalPreparation
set_option maxHeartbeats 1500000

def zeroWork {n : ℕ} {input : BinaryTerminalGrouping.Input n} (prepared : Prepared input) : Prepared input :=
  { prepared with prefixWork := 0 }

def certify {n : ℕ} {input : BinaryTerminalGrouping.Input n} (cached : CacheData input)
    (h : cached = erase (prepare input)) : Prepared input :=
  { count := cached.count
    packing := cached.packing
    totals := cached.totals
    routes := cached.routes
    pivot := cached.pivot
    ell := cached.ell
    probability := cached.probability
    prefixWork := 0
    count_eq := by cases h; exact (prepare input).count_eq
    packing_eq := by cases h; exact (prepare input).packing_eq
    totals_eq := by cases h; exact (prepare input).totals_eq
    routes_eq := by cases h; exact (prepare input).routes_eq
    pivot_eq := by cases h; exact (prepare input).pivot_eq
    ell_eq := by cases h; exact (prepare input).ell_eq
    probability_eq := by cases h; exact (prepare input).probability_eq }

theorem certify_exact {n : ℕ} {input : BinaryTerminalGrouping.Input n} (cached : CacheData input)
    (h : cached = erase (prepare input)) : certify cached h = zeroWork (prepare input) := by
  cases h
  rfl

theorem certify_data {n : ℕ} {input : BinaryTerminalGrouping.Input n} (cached : CacheData input)
    (h : cached = erase (prepare input)) : erase (certify cached h) = cached := rfl

def certifyWithTrace {n : ℕ} {input : BinaryTerminalGrouping.Input n} (cached : CacheData input)
    (h : cached = erase (prepare input)) : Prepared input × Trace :=
  (certify cached h,wrap 64 2 [])

theorem certifyWithTrace_usage {n : ℕ} {input : BinaryTerminalGrouping.Input n} (cached : CacheData input)
    (h : cached = erase (prepare input)) : usage (certifyWithTrace cached h).2 ≤ 66 := by
  have hBound := wrap_usage 64 2 []
  change usage (wrap 64 2 []) ≤ 66
  simpa only [List.map_nil,List.sum_nil,Nat.add_zero] using hBound

theorem zeroWork_uniform {n : ℕ} {input : BinaryTerminalGrouping.Input n} (prepared : Prepared input) :
    (zeroWork prepared).uniform = prepared.uniform := rfl

theorem zeroWork_mixed {n : ℕ} {input : BinaryTerminalGrouping.Input n} (prepared : Prepared input) :
    (zeroWork prepared).mixed = prepared.mixed := rfl

theorem zeroWork_runPrepared {n : ℕ} (store : BinarySeedLookupTree.Store) {input : BinaryTerminalGrouping.Input n}
    (prepared : Prepared input) (hC : input.Canonical) (hAd : BinaryTerminalPromises.Admissible input)
    (K : ℕ) (outer scalar : Fin K → Bool) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    BinaryPRGWordControllerTerminal.runPrepared store (zeroWork prepared) hC hAd K outer scalar pc hp =
      BinaryPRGWordControllerTerminal.runPrepared store prepared hC hAd K outer scalar pc hp := by
  rfl

end Blotto.BinaryTerminalCacheCertificate
