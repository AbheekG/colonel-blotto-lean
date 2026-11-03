import Blotto.BinaryScalarTape
import Blotto.BinaryPRGHeapUniformTerminalLifetime

/-! Original request fields derive a uniform polynomial for the complete
physical resource/cache/uniform-terminal trace, including exhausted prefixes.
The explicit uniform-branch premise specifies this entry point's scope. -/
namespace Blotto.BinaryPRGHeapUniformTerminalPolynomial
open BinaryPRGHeapTraceUsage BinaryPRGHeapUniformTerminalLifetime BinaryCachedGroupInputHeight
set_option maxHeartbeats 2000000

theorem envelope_polynomial : ∃ C d : ℕ,∀ {n : ℕ} (request : BinaryPRGRequest.Request n) (K i b : ℕ),
    envelope request K i b ≤ C * (n + request.source.originalInputWordWidth + K + i + b + 2)^d := by
  rcases BinaryPRGHeapCallerLifetimePolynomial.uniform_cached_envelope with ⟨C₁,d₁,h₁⟩
  rcases BinaryWordUniformTerminalLifetime.envelope_polynomial with ⟨C₂,d₂,h₂⟩
  refine ⟨C₁ + C₂ * 7^d₂ + 160,max d₁ d₂,?_⟩
  intro n request K i b
  let X := n + request.source.originalInputWordWidth + K + i + b + 2
  let D := max d₁ d₂
  have hX : 0 < X := by dsimp [X]; omega
  have hPrefix := h₁ request i b
  have hTerm := h₂ n (inputHeight request) K i b
  have hPrefixSize : n + request.source.originalInputWordWidth + i + b + 2 ≤ X := by dsimp [X]; omega
  have hTermSize : n + inputHeight request + K + i + b + 5 ≤ 7 * X := by
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
    (hUniform : UniformBranch store request rich) (K : ℕ) (scalar : BinaryScalarTape K),
    usage (runWithTrace store request rich hUniform K scalar).2 ≤
      C * (n + request.source.originalInputWordWidth + K + store.width + store.cap.value + 2)^d := by
  rcases envelope_polynomial with ⟨C,d,hBound⟩
  exact ⟨C,d,fun store request rich hUniform K scalar =>
    (runWithTrace_usage store request rich hUniform K scalar).trans (hBound request K store.width store.cap.value)⟩

open BinarySeedPreparationSpace in
theorem uniform_all_prefix : ∃ C d : ℕ,∀ {n : ℕ} (store : BinarySeedLookupTree.Store) (request : BinaryPRGRequest.Request n) (rich : Bool)
    (hUniform : UniformBranch store request rich) (K : ℕ) (scalar : BinaryScalarTape K) (borrowed steps : ℕ),
    retainedHeap borrowed (runWithTrace store request rich hUniform K scalar).2 steps ≤
        borrowed + C * (n + request.source.originalInputWordWidth + K + store.width + store.cap.value + 2)^d ∧
      framePeak ((runWithTrace store request rich hUniform K scalar).2.take steps) ≤
        C * (n + request.source.originalInputWordWidth + K + store.width + store.cap.value + 2)^d := by
  rcases uniform_usage with ⟨C,d,hBound⟩
  exact ⟨C,d,fun store request rich hUniform K scalar borrowed steps =>
    BinaryPRGHeapTraceUsage.all_prefix _ _ (hBound store request rich hUniform K scalar) borrowed steps⟩

end Blotto.BinaryPRGHeapUniformTerminalPolynomial
