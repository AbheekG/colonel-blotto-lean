import Blotto.BinaryScalarTape
import Blotto.BinaryPRGHeapCertifiedPrefixProperties
import Blotto.BinaryWordSmallTerminalLifetime

/-! One physical resource/cache prefix feeds its actual retained fields and
cursor to uniform-two, uniform-three or mixed-two terminal dispatch. The
explicit branch condition excludes mixed-three; fallback/output/raw parsing
and host-space interpretation remain separate continuation obligations. -/
namespace Blotto.BinaryPRGHeapSmallTerminalLifetime
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryPRGResourceWork BinaryPRGTerminalWork BinaryCachedGroupInputHeight
open BinaryPRGHeapCertifiedPrefixLifetime
set_option maxHeartbeats 2000000

def SmallBranch {n : ℕ} (store : BinarySeedLookupTree.Store) (request : BinaryPRGRequest.Request n) (rich : Bool) : Prop :=
  ∀ result : CachedResult request rich,(BinaryPRGHeapCertifiedPrefixLifetime.runWithTrace store request rich).1.1 = some result →
    BinaryWordSmallTerminalLifetime.SmallBranch result.2

def runWithTrace {n : ℕ} (store : BinarySeedLookupTree.Store) (request : BinaryPRGRequest.Request n) (rich : Bool)
    (hSmall : SmallBranch store request rich) (K : ℕ) (scalar : BinaryScalarTape K) :
    BinaryPRGWordControllerTerminal.Result store n × Trace :=
  let observed := BinaryPRGHeapCertifiedPrefixLifetime.runWithTrace store request rich
  match hs : observed.1.1 with
  | none => ((none,observed.1.2),wrap 16 2 [observed.2])
  | some result =>
      let drawn := BinaryWordSmallTerminalLifetime.runWithTrace store result.2
        (terminal_canonical request rich result.1) (BinaryPRGHeapCertifiedPrefixProperties.admissible store request rich result hs)
        (hSmall result hs) K scalar observed.1.2 (BinaryPRGHeapCertifiedPrefixProperties.cursor_bound store request rich)
      (drawn.1,wrap 32 2 [observed.2,drawn.2])

theorem runWithTrace_none {n : ℕ} (store : BinarySeedLookupTree.Store) (request : BinaryPRGRequest.Request n) (rich : Bool)
    (hSmall : SmallBranch store request rich) (K : ℕ) (scalar : BinaryScalarTape K)
    (h : (BinaryPRGHeapCertifiedPrefixLifetime.runWithTrace store request rich).1.1 = none) :
    (runWithTrace store request rich hSmall K scalar).1 =
      (none,(BinaryPRGHeapCertifiedPrefixLifetime.runWithTrace store request rich).1.2) := by
  unfold runWithTrace
  dsimp only
  split
  · rfl
  · rename_i result hOther
    cases h.symm.trans hOther

theorem runWithTrace_some {n : ℕ} (store : BinarySeedLookupTree.Store) (request : BinaryPRGRequest.Request n) (rich : Bool)
    (hSmall : SmallBranch store request rich) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (result : CachedResult request rich)
    (h : (BinaryPRGHeapCertifiedPrefixLifetime.runWithTrace store request rich).1.1 = some result) :
    (runWithTrace store request rich hSmall K scalar).1 =
      BinaryPRGWordControllerTerminal.runPrepared store
        (BinaryCachedTerminalPreparation.prepare (terminalInput request rich result.1))
        (terminal_canonical request rich result.1) (BinaryPRGHeapCertifiedPrefixProperties.admissible store request rich result h)
        K outer scalar (BinaryPRGHeapCertifiedPrefixLifetime.runWithTrace store request rich).1.2
        (BinaryPRGHeapCertifiedPrefixProperties.cursor_bound store request rich) := by
  unfold runWithTrace
  dsimp only
  split
  · rename_i hOther
    cases hOther.symm.trans h
  · rename_i other hOther
    have he : other = result := Option.some.inj (hOther.symm.trans h)
    subst other
    rw [BinaryWordSmallTerminalLifetime.runWithTrace_erasure _ _ _ _ _ K outer]
    rw [(BinaryPRGHeapCertifiedPrefixProperties.reached store request rich result h).2]
    exact BinaryTerminalCacheCertificate.zeroWork_runPrepared _ _ _ _ _ _ _ _ _

noncomputable def envelope {n : ℕ} (request : BinaryPRGRequest.Request n) (K indexWidth seedCap : ℕ) : ℕ :=
  BinaryPRGHeapCertifiedPrefixLifetime.envelope request indexWidth seedCap +
    BinaryWordSmallTerminalLifetime.envelope n (inputHeight request) K indexWidth seedCap + 64

theorem runWithTrace_usage {n : ℕ} (store : BinarySeedLookupTree.Store) (request : BinaryPRGRequest.Request n) (rich : Bool)
    (hSmall : SmallBranch store request rich) (K : ℕ) (scalar : BinaryScalarTape K) :
    usage (runWithTrace store request rich hSmall K scalar).2 ≤ envelope request K store.width store.cap.value := by
  let observed := BinaryPRGHeapCertifiedPrefixLifetime.runWithTrace store request rich
  have hPrefix := BinaryPRGHeapCertifiedPrefixLifetime.runWithTrace_usage store request rich
  change usage observed.2 ≤ _ at hPrefix
  unfold runWithTrace
  dsimp only
  split
  · have hw := wrap_usage 16 2 [observed.2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change usage (wrap 16 2 [observed.2]) ≤ _
    unfold envelope
    omega
  · rename_i result hSome
    have hs : 3 ≤ inputHeight request := by unfold inputHeight; omega
    let drawn := BinaryWordSmallTerminalLifetime.runWithTrace store result.2
      (terminal_canonical request rich result.1) (BinaryPRGHeapCertifiedPrefixProperties.admissible store request rich result hSome)
      (hSmall result hSome) K scalar observed.1.2 (BinaryPRGHeapCertifiedPrefixProperties.cursor_bound store request rich)
    have hDraw := BinaryWordSmallTerminalLifetime.runWithTrace_usage store result.2
      (terminal_canonical request rich result.1) (BinaryPRGHeapCertifiedPrefixProperties.admissible store request rich result hSome)
      (hSmall result hSome) (inputHeight request) hs (BinaryPRGHeapCertifiedPrefixProperties.uniform_height store request rich result hSome)
      (BinaryPRGHeapCertifiedPrefixProperties.mixed_height store request rich result hSome)
      (BinaryPRGHeapCertifiedPrefixProperties.route_height store request rich result hSome)
      K scalar observed.1.2 (BinaryPRGHeapCertifiedPrefixProperties.cursor_bound store request rich)
    change usage drawn.2 ≤ _ at hDraw
    have hw := wrap_usage 32 2 [observed.2,drawn.2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change usage (wrap 32 2 [observed.2,drawn.2]) ≤ _
    unfold envelope
    omega

theorem envelope_polynomial : ∃ C d : ℕ,∀ {n : ℕ} (request : BinaryPRGRequest.Request n) (K i b : ℕ),
    envelope request K i b ≤ C * (n + request.source.originalInputWordWidth + K + i + b + 2)^d := by
  rcases BinaryPRGHeapCallerLifetimePolynomial.uniform_cached_envelope with ⟨C₁,d₁,h₁⟩
  rcases BinaryWordSmallTerminalLifetime.envelope_polynomial with ⟨C₂,d₂,h₂⟩
  refine ⟨C₁ + C₂ * 7^d₂ + 160,max d₁ d₂,?_⟩
  intro n request K i b
  let X := n + request.source.originalInputWordWidth + K + i + b + 2
  let D := max d₁ d₂
  have hX : 0 < X := by dsimp [X]; omega
  have hPrefix := h₁ request i b
  have hTerm := h₂ n (inputHeight request) K i b
  have hPrefixSize : n + request.source.originalInputWordWidth + i + b + 2 ≤ X := by dsimp [X]; omega
  have hTermSize : n + inputHeight request + K + i + b + 2 ≤ 7 * X := by
    unfold inputHeight
    dsimp [X]
    omega
  have hP₁ := (Nat.pow_le_pow_left hPrefixSize d₁).trans
    (Nat.pow_le_pow_right hX (show d₁ ≤ D from le_max_left _ _))
  have hP₂ := Nat.pow_le_pow_left hTermSize d₂
  rw [Nat.mul_pow] at hP₂
  have hD₂ : X^d₂ ≤ X^D := Nat.pow_le_pow_right hX (le_max_right _ _)
  have hP₂' := hP₂.trans (Nat.mul_le_mul_left (7^d₂) hD₂)
  have hA := Nat.mul_le_mul_left C₁ hP₁
  have hB := Nat.mul_le_mul_left C₂ hP₂'
  have hOne : 1 ≤ X^D := Nat.one_le_pow _ _ hX
  change envelope request K i b ≤ (C₁ + C₂ * 7^d₂ + 160) * X^D
  unfold envelope BinaryPRGHeapCertifiedPrefixLifetime.envelope
  nlinarith

theorem uniform_usage : ∃ C d : ℕ,∀ {n : ℕ} (store : BinarySeedLookupTree.Store) (request : BinaryPRGRequest.Request n) (rich : Bool)
    (hSmall : SmallBranch store request rich) (K : ℕ) (scalar : BinaryScalarTape K),
    usage (runWithTrace store request rich hSmall K scalar).2 ≤
      C * (n + request.source.originalInputWordWidth + K + store.width + store.cap.value + 2)^d := by
  rcases envelope_polynomial with ⟨C,d,hBound⟩
  exact ⟨C,d,fun store request rich hSmall K scalar =>
    (runWithTrace_usage store request rich hSmall K scalar).trans (hBound request K store.width store.cap.value)⟩

theorem uniform_all_prefix : ∃ C d : ℕ,∀ {n : ℕ} (store : BinarySeedLookupTree.Store) (request : BinaryPRGRequest.Request n) (rich : Bool)
    (hSmall : SmallBranch store request rich) (K : ℕ) (scalar : BinaryScalarTape K) (borrowed steps : ℕ),
    retainedHeap borrowed (runWithTrace store request rich hSmall K scalar).2 steps ≤
        borrowed + C * (n + request.source.originalInputWordWidth + K + store.width + store.cap.value + 2)^d ∧
      framePeak ((runWithTrace store request rich hSmall K scalar).2.take steps) ≤
        C * (n + request.source.originalInputWordWidth + K + store.width + store.cap.value + 2)^d := by
  rcases uniform_usage with ⟨C,d,hBound⟩
  exact ⟨C,d,fun store request rich hSmall K scalar borrowed steps =>
    BinaryPRGHeapTraceUsage.all_prefix _ _ (hBound store request rich hSmall K scalar) borrowed steps⟩

end Blotto.BinaryPRGHeapSmallTerminalLifetime
