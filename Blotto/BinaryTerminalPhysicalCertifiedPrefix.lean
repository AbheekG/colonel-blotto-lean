import Blotto.BinaryTerminalPhysicalRouteLifetime
import Blotto.BinaryPRGHeapCertifiedPrefixLifetime

/-! Reattach the terminal certificate to the cache returned by the parallel
physical route. The parser success witness is erased proof data; the runner
does not recompute the reference cache. -/
namespace Blotto.BinaryTerminalPhysicalCertifiedPrefix
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage BinaryPRGResourceWork
open BinaryPRGTerminalWork BinaryTerminalCacheLifetime BinaryTerminalCacheCertificate
open BinaryTerminalPhysicalRouteLifetime
set_option maxHeartbeats 2000000

theorem accepted_cache_correct (frame : List Bool)
    (parsed : (Σ n, BinaryPRGPhysicalRawRequestLifetime.Request n) × List Bool)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool)
    (result : BinaryPRGHeapCachedPrefixLifetime.CachedResult parsed.1.2.logical.request rich)
    (h : (runCachedPrefixWithTrace parsed.1 seed rich).1.1 = some result) :
    result.2 = erase (BinaryCachedTerminalPreparation.prepare
      (terminalInput parsed.1.2.logical.request rich result.1)) := by
  rw [accepted_cached_prefix_erases frame parsed hParsed seed rich] at h
  exact BinaryPRGHeapCertifiedPrefixLifetime.cache_correct seed
    parsed.1.2.logical.request rich result h

def runWithTrace (frame : List Bool)
    (parsed : (Σ n, BinaryPRGPhysicalRawRequestLifetime.Request n) × List Bool)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) :
    (Option (BinaryPRGHeapCertifiedPrefixLifetime.CachedResult
      parsed.1.2.logical.request rich) × FixedBinaryWord seed.width) × Trace :=
  let observed := runCachedPrefixWithTrace parsed.1 seed rich
  match hs : observed.1.1 with
  | none => ((none,observed.1.2),wrap 16 2 [observed.2])
  | some result =>
      let certified := certifyWithTrace result.2
        (accepted_cache_correct frame parsed hParsed seed rich result hs)
      ((some ⟨result.1,certified.1⟩,observed.1.2),
        wrap 24 2 [observed.2,certified.2])

theorem runWithTrace_erasure (frame : List Bool)
    (parsed : (Σ n, BinaryPRGPhysicalRawRequestLifetime.Request n) × List Bool)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) :
    (runWithTrace frame parsed hParsed seed rich).1 =
      let observed := runCachedPrefixWithTrace parsed.1 seed rich
      (observed.1.1.map (fun result =>
        (⟨result.1,zeroWork (BinaryCachedTerminalPreparation.prepare
          (terminalInput parsed.1.2.logical.request rich result.1))⟩ :
          BinaryPRGHeapCertifiedPrefixLifetime.CachedResult
            parsed.1.2.logical.request rich)),observed.1.2) := by
  unfold runWithTrace
  dsimp only
  split
  · rename_i hNone
    simp only [hNone,Option.map_none]
    rfl
  · rename_i result hSome
    simp only [hSome,Option.map_some,certifyWithTrace,certify_exact]
    rfl

theorem accepted_reference (frame : List Bool)
    (parsed : (Σ n, BinaryPRGPhysicalRawRequestLifetime.Request n) × List Bool)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) :
    (runWithTrace frame parsed hParsed seed rich).1 =
      BinaryPRGHeapCertifiedPrefixLifetime.reference seed
        parsed.1.2.logical.request rich := by
  rw [runWithTrace_erasure]
  have h := congrArg (fun observed :
      Option (BinaryPRGHeapCachedPrefixLifetime.CachedResult
        parsed.1.2.logical.request rich) × FixedBinaryWord seed.width =>
      (observed.1.map (fun result =>
        (⟨result.1,zeroWork (BinaryCachedTerminalPreparation.prepare
          (terminalInput parsed.1.2.logical.request rich result.1))⟩ :
          BinaryPRGHeapCertifiedPrefixLifetime.CachedResult
            parsed.1.2.logical.request rich)),observed.2))
    (accepted_cached_prefix_reference frame parsed hParsed seed rich)
  apply h.trans
  unfold BinaryPRGHeapCachedPrefixLifetime.reference
    BinaryPRGHeapCertifiedPrefixLifetime.reference
  dsimp only
  cases (BinaryPRGWordControllerResource.requestRun seed
    parsed.1.2.logical.request rich).1 <;> rfl

theorem accepted_logical_output (frame : List Bool)
    (parsed : (Σ n, BinaryPRGPhysicalRawRequestLifetime.Request n) × List Bool)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) :
    (runWithTrace frame parsed hParsed seed rich).1 =
      (BinaryPRGHeapCertifiedPrefixLifetime.runWithTrace seed
        parsed.1.2.logical.request rich).1 := by
  rw [accepted_reference frame parsed hParsed seed rich,
    BinaryPRGHeapCertifiedPrefixLifetime.runWithTrace_reference]

noncomputable def envelope (frame : List Bool)
    (parsed : Σ n, BinaryPRGPhysicalRawRequestLifetime.Request n)
    (seed : BinarySeedLookupTree.Store) : ℕ :=
  cachedPrefixEnvelope frame parsed seed + 96

theorem accepted_usage_additive (frame : List Bool)
    (parsed : (Σ n, BinaryPRGPhysicalRawRequestLifetime.Request n) × List Bool)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) :
    usage (runWithTrace frame parsed hParsed seed rich).2 ≤
      usage (runCachedPrefixWithTrace parsed.1 seed rich).2 + 96 := by
  unfold runWithTrace
  dsimp only
  split
  · rename_i hNone
    have hw := wrap_usage 16 2 [(runCachedPrefixWithTrace parsed.1 seed rich).2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    dsimp only
    omega
  · rename_i result hSome
    have hCert := certifyWithTrace_usage result.2
      (accepted_cache_correct frame parsed hParsed seed rich result hSome)
    have hw := wrap_usage 24 2 [(runCachedPrefixWithTrace parsed.1 seed rich).2,
      (certifyWithTrace result.2
        (accepted_cache_correct frame parsed hParsed seed rich result hSome)).2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    dsimp only
    omega

theorem accepted_usage (frame : List Bool)
    (parsed : (Σ n, BinaryPRGPhysicalRawRequestLifetime.Request n) × List Bool)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) :
    usage (runWithTrace frame parsed hParsed seed rich).2 ≤
      envelope frame parsed.1 seed := by
  have hAdd := accepted_usage_additive frame parsed hParsed seed rich
  have hPrefix := accepted_cached_prefix_usage frame parsed hParsed seed rich
  unfold envelope
  omega

theorem accepted_uniform_polynomial :
    ∃ C d : ℕ, ∀ (frame : List Bool)
      (parsed : (Σ n, BinaryPRGPhysicalRawRequestLifetime.Request n) × List Bool)
      (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
      (seed : BinarySeedLookupTree.Store) (rich : Bool),
      usage (runWithTrace frame parsed hParsed seed rich).2 ≤
        C*(frame.length+seed.width+seed.cap.value+3)^d := by
  obtain ⟨C,d,hCached⟩ := accepted_cached_prefix_uniform_polynomial
  refine ⟨C+96,d,?_⟩
  intro frame parsed hParsed seed rich
  have h := accepted_usage_additive frame parsed hParsed seed rich
  have hC := hCached frame parsed hParsed seed rich
  have hOne := Nat.one_le_pow d
    (frame.length+seed.width+seed.cap.value+3) (by omega)
  nlinarith

theorem accepted_all_prefix (frame : List Bool)
    (parsed : (Σ n, BinaryPRGPhysicalRawRequestLifetime.Request n) × List Bool)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (borrowed steps : ℕ) :
    retainedHeap borrowed (runWithTrace frame parsed hParsed seed rich).2 steps ≤
        borrowed+envelope frame parsed.1 seed ∧
      framePeak ((runWithTrace frame parsed hParsed seed rich).2.take steps) ≤
        envelope frame parsed.1 seed :=
  BinaryPRGHeapTraceUsage.all_prefix _ _
    (accepted_usage frame parsed hParsed seed rich) borrowed steps

end Blotto.BinaryTerminalPhysicalCertifiedPrefix
