import Blotto.BinaryPRGHeapCachedPrefixLifetime
import Blotto.BinaryPRGHeapReflectedLifetime

/-! Original caller fields supply uniform allocation/activation polynomials
for the physical request-to-cache prefix and complete reflected setup/source.
They do not include the subsequent selected terminal/output continuation. -/
namespace Blotto.BinaryPRGHeapCallerLifetimePolynomial
open BinaryPRGHeapResourcePolynomial BinaryPRGHeapTraceUsage
set_option maxHeartbeats 3000000

def cachedEnvelope (n S D indexWidth seedCap : ℕ) : ℕ :=
  BinaryPRGHeapNativeLifetimeBound.envelope n (BinaryPRGWordControllerBooleanResourceLoopWork.widthBound D)
    D indexWidth seedCap + 28 + 2 * indexWidth + BinaryTerminalCacheLifetime.envelope n S + 4 * n + 80

theorem cached_envelope_polynomial : NaturalPolynomialEnvelope inputSize
    (fun p => cachedEnvelope p.count p.wordWidth p.denominator p.seedWidth p.seedCap) := by
  simp only [cachedEnvelope,BinaryTerminalCacheLifetime.envelope,
    BinaryTerminalPrefixLifetime.packingStepBound,BinaryTerminalRouteLifetime.routeBound,
    BinaryPRGWordControllerBooleanResourceLoopWork.widthBound]
  unfold_native_lifetime_envelope
  unfold_heap_lifetime_envelope
  resource_polynomial

theorem reflected_envelope_polynomial : NaturalPolynomialEnvelope inputSize
    (fun p => BinaryPRGHeapReflectedLifetime.envelope p.wordWidth p.seedWidth p.seedCap) := by
  simp only [BinaryPRGHeapReflectedLifetime.envelope,BinaryReflectedPreparationLifetime.envelope,
    BinaryReflectedParameterLifetime.envelope,BinaryReflectedSystemLifetime.envelope,
    BinaryReflectedSystemLifetime.capacityEnvelope,BinaryLifetimeUsage.opcodeEnvelope,
    BinaryQuadraticSyntaxLifetime.bound,BinaryQuadraticSyntaxLifetime.frames,
    BinaryQuadraticExpressionLifetime.stepBound,BinaryQuadraticExpressionLifetime.frameBound,
    BinaryQuadraticLifetime.opcodeBound,BinaryQuadraticLifetime.opcodeFrames]
  unfold_native_lifetime_envelope
  unfold_heap_lifetime_envelope
  resource_polynomial

theorem uniform_cached_envelope : ∃ C d : ℕ,∀ {n : ℕ} (request : BinaryPRGRequest.Request n) (indexWidth seedCap : ℕ),
    BinaryPRGHeapCachedPrefixLifetime.envelope request indexWidth seedCap ≤
      C * (n + request.source.originalInputWordWidth + indexWidth + seedCap + 2)^d := by
  rcases cached_envelope_polynomial with ⟨C,d,hBound⟩
  refine ⟨C * 2^d,d,?_⟩
  intro n request indexWidth seedCap
  have h := hBound ⟨n,request.source.originalInputWordWidth,request.source.normalizedInput.latticeDenominator,indexWidth,seedCap⟩
  have hWidth := request.source.normalized_lattice_wordWidth_original
  have hSize : inputSize ⟨n,request.source.originalInputWordWidth,request.source.normalizedInput.latticeDenominator,indexWidth,seedCap⟩ + 1 ≤
      2 * (n + request.source.originalInputWordWidth + indexWidth + seedCap + 2) := by
    unfold inputSize
    dsimp only
    omega
  have hp := Nat.mul_le_mul_left C (Nat.pow_le_pow_left hSize d)
  rw [Nat.mul_pow] at hp
  exact h.trans (hp.trans_eq (by ring))

theorem uniform_cached_usage : ∃ C d : ℕ,∀ {n : ℕ} (seed : BinarySeedLookupTree.Store)
    (request : BinaryPRGRequest.Request n) (rich : Bool),
    usage (BinaryPRGHeapCachedPrefixLifetime.runWithTrace seed request rich).2 ≤
      C * (n + request.source.originalInputWordWidth + seed.width + seed.cap.value + 2)^d := by
  rcases uniform_cached_envelope with ⟨C,d,hBound⟩
  exact ⟨C,d,fun seed request rich => (BinaryPRGHeapCachedPrefixLifetime.runWithTrace_usage seed request rich).trans
    (hBound request seed.width seed.cap.value)⟩

theorem uniform_reflected_usage : ∃ C d : ℕ,
    ∀ (seed : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (source : RationalFourInput)
      (hC : input.Canonical),input.Refines source → source.w < (1 - source.p) * source.ell →
      ∀ s,2 ≤ s → source.FieldsHeight s → ∀ (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value),
    usage (BinaryPRGHeapReflectedLifetime.runWithTrace seed input hC pc hp).2 ≤ C * (s + seed.width + seed.cap.value + 2)^d := by
  rcases reflected_envelope_polynomial with ⟨C,d,hBound⟩
  refine ⟨C,d,?_⟩
  intro seed input source hC hR hCase s hs hH pc hp
  have h := (BinaryPRGHeapReflectedLifetime.runWithTrace_usage seed input source hC hR hCase s hs hH pc hp).trans
    (hBound ⟨0,s,0,seed.width,seed.cap.value⟩)
  have he : inputSize ⟨0,s,0,seed.width,seed.cap.value⟩ + 1 = s + seed.width + seed.cap.value + 2 := by
    simp [inputSize,binaryWordWidth]
    omega
  simpa only [he] using h

end Blotto.BinaryPRGHeapCallerLifetimePolynomial
