import Blotto.BinaryPRGHeapCallerLifetimePolynomial
import Blotto.BinaryTerminalCacheCertificate

/-! Reattach proof fields to the cache actually returned by the physical
request, retaining the whole prefix. No cache or source production is replayed.
The previous work annotation is absent from the new terminal data path. -/
namespace Blotto.BinaryPRGHeapCertifiedPrefixLifetime
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage BinaryPRGResourceWork BinaryPRGTerminalWork
open BinaryTerminalCacheLifetime BinaryTerminalCacheCertificate
set_option maxHeartbeats 2000000

def CachedResult {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool) :=
  Σ state : BinaryResourcePair.Certified (resourceInput request rich).length,
    BinaryCachedTerminalPreparation.Prepared (terminalInput request rich state)

theorem cache_correct {n : ℕ} (store : BinarySeedLookupTree.Store) (request : BinaryPRGRequest.Request n) (rich : Bool)
    (result : BinaryPRGHeapCachedPrefixLifetime.CachedResult request rich)
    (h : (BinaryPRGHeapCachedPrefixLifetime.runWithTrace store request rich).1.1 = some result) :
    result.2 = erase (BinaryCachedTerminalPreparation.prepare (terminalInput request rich result.1)) := by
  rw [BinaryPRGHeapCachedPrefixLifetime.runWithTrace_erasure] at h
  unfold BinaryPRGHeapCachedPrefixLifetime.reference at h
  dsimp only at h
  obtain ⟨state,hState,hResult⟩ := Option.map_eq_some_iff.mp h
  cases hResult
  rfl

def runWithTrace {n : ℕ} (store : BinarySeedLookupTree.Store) (request : BinaryPRGRequest.Request n) (rich : Bool) :
    (Option (CachedResult request rich) × FixedBinaryWord store.width) × Trace :=
  let observed := BinaryPRGHeapCachedPrefixLifetime.runWithTrace store request rich
  match hs : observed.1.1 with
  | none => ((none,observed.1.2),wrap 16 2 [observed.2])
  | some result =>
      let certified := certifyWithTrace result.2 (cache_correct store request rich result hs)
      ((some ⟨result.1,certified.1⟩,observed.1.2),wrap 24 2 [observed.2,certified.2])

theorem runWithTrace_erasure {n : ℕ} (store : BinarySeedLookupTree.Store) (request : BinaryPRGRequest.Request n) (rich : Bool) :
    (runWithTrace store request rich).1 =
      let observed := BinaryPRGHeapCachedPrefixLifetime.runWithTrace store request rich
      (observed.1.1.map (fun result => (⟨result.1,zeroWork (BinaryCachedTerminalPreparation.prepare
        (terminalInput request rich result.1))⟩ : CachedResult request rich)),observed.1.2) := by
  unfold runWithTrace
  dsimp only
  split
  · rename_i hNone
    simp only [hNone,Option.map_none]
    rfl
  · rename_i result hSome
    simp only [hSome,Option.map_some,certifyWithTrace,certify_exact]
    rfl

def reference {n : ℕ} (store : BinarySeedLookupTree.Store) (request : BinaryPRGRequest.Request n) (rich : Bool) :
    Option (CachedResult request rich) × FixedBinaryWord store.width :=
  let observed := BinaryPRGWordControllerResource.requestRun store request rich
  (observed.1.map (fun state => ⟨state,zeroWork (BinaryCachedTerminalPreparation.prepare (terminalInput request rich state))⟩),observed.2)

theorem runWithTrace_reference {n : ℕ} (store : BinarySeedLookupTree.Store) (request : BinaryPRGRequest.Request n) (rich : Bool) :
    (runWithTrace store request rich).1 = reference store request rich := by
  rw [runWithTrace_erasure]
  have h := congrArg (fun observed : Option (BinaryPRGHeapCachedPrefixLifetime.CachedResult request rich) × FixedBinaryWord store.width =>
    (observed.1.map (fun result => (⟨result.1,zeroWork (BinaryCachedTerminalPreparation.prepare
      (terminalInput request rich result.1))⟩ : CachedResult request rich)),observed.2))
    (BinaryPRGHeapCachedPrefixLifetime.runWithTrace_erasure store request rich)
  apply h.trans
  unfold BinaryPRGHeapCachedPrefixLifetime.reference reference
  dsimp only
  cases (BinaryPRGWordControllerResource.requestRun store request rich).1 <;> rfl

noncomputable def envelope {n : ℕ} (request : BinaryPRGRequest.Request n) (indexWidth seedCap : ℕ) : ℕ :=
  BinaryPRGHeapCachedPrefixLifetime.envelope request indexWidth seedCap + 96

theorem runWithTrace_usage {n : ℕ} (store : BinarySeedLookupTree.Store) (request : BinaryPRGRequest.Request n) (rich : Bool) :
    usage (runWithTrace store request rich).2 ≤ envelope request store.width store.cap.value := by
  have hPrefix := BinaryPRGHeapCachedPrefixLifetime.runWithTrace_usage store request rich
  unfold runWithTrace
  dsimp only
  split
  · rename_i hNone
    have hw := wrap_usage 16 2 [(BinaryPRGHeapCachedPrefixLifetime.runWithTrace store request rich).2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    dsimp only
    unfold envelope
    omega
  · rename_i result hSome
    have hCert := certifyWithTrace_usage result.2 (cache_correct store request rich result hSome)
    have hw := wrap_usage 24 2 [(BinaryPRGHeapCachedPrefixLifetime.runWithTrace store request rich).2,
      (certifyWithTrace result.2 (cache_correct store request rich result hSome)).2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    dsimp only
    unfold envelope
    omega

theorem uniform_usage : ∃ C d : ℕ,∀ {n : ℕ} (store : BinarySeedLookupTree.Store) (request : BinaryPRGRequest.Request n) (rich : Bool),
    usage (runWithTrace store request rich).2 ≤ C * (n + request.source.originalInputWordWidth + store.width + store.cap.value + 2)^d := by
  rcases BinaryPRGHeapCallerLifetimePolynomial.uniform_cached_envelope with ⟨C,d,hBound⟩
  refine ⟨C + 96,d,?_⟩
  intro n store request rich
  have h := runWithTrace_usage store request rich
  have hE := hBound request store.width store.cap.value
  have hOne := Nat.one_le_pow d (n + request.source.originalInputWordWidth + store.width + store.cap.value + 2) (by omega)
  unfold envelope at h
  nlinarith

theorem all_prefix {n : ℕ} (store : BinarySeedLookupTree.Store) (request : BinaryPRGRequest.Request n) (rich : Bool) (borrowed steps : ℕ) :
    retainedHeap borrowed (runWithTrace store request rich).2 steps ≤ borrowed + envelope request store.width store.cap.value ∧
      framePeak ((runWithTrace store request rich).2.take steps) ≤ envelope request store.width store.cap.value :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (runWithTrace_usage store request rich) borrowed steps

end Blotto.BinaryPRGHeapCertifiedPrefixLifetime
