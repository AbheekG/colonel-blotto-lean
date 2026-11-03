import Blotto.BinaryScalarTape
import Blotto.BinaryWordGroupEmissionLifetime
import Blotto.BinaryWordTerminalLifetimePolynomial

/-! Uniform polynomial source-cell/activation bounds for the complete cached
uniform and mixed-two factory/draw/emission paths. The original field and seed
parameters suffice; no descriptor or selected-row price is an input. -/
namespace Blotto.BinaryWordGroupLifetimePolynomial
open BinaryPRGHeapResourcePolynomial BinaryPRGHeapTraceUsage
set_option maxHeartbeats 3000000

macro "unfold_word_group_envelope" : tactic => `(tactic|
  simp only [BinaryWordGroupEmissionLifetime.uniformEnvelope,BinaryWordGroupEmissionLifetime.mixedEnvelope,
    BinaryWordGroupEmissionLifetime.groupHeight,BinaryWordGroupLifetime.uniformEnvelope,BinaryWordGroupLifetime.mixedEnvelope,
    BinaryGroupFactoryLifetime.uniformEnvelope,BinaryGroupFactoryLifetime.mixedEnvelope,
    BinaryUnorderedThreeLifetime.envelope,BinaryOrderedThreeLifetimeBound.envelope,
    BinaryThreeGeometryLifetime.regimeEnvelope,BinaryThreeGeometryLifetime.geometryEnvelope,
    BinaryThreeGeometryLifetime.comparisonEnvelope,BinaryQuadraticThreeFactoryLifetime.bound,
    BinaryQuadraticThreeFactoryLifetime.frames,BinaryQuadraticThreeFactoryLifetime.expressionBound,
    BinaryQuadraticThreeFactoryLifetime.expressionFrames]
  <;> unfold_word_terminal_envelope)

theorem uniform_diagonal_polynomial : NaturalPolynomialEnvelope inputSize (fun p =>
    BinaryWordGroupEmissionLifetime.uniformEnvelope p.wordWidth p.wordWidth p.wordWidth p.wordWidth p.wordWidth p.wordWidth) := by
  unfold_word_group_envelope
  resource_polynomial

theorem mixed_diagonal_polynomial : NaturalPolynomialEnvelope inputSize (fun p =>
    BinaryWordGroupEmissionLifetime.mixedEnvelope p.wordWidth p.wordWidth p.wordWidth p.wordWidth p.wordWidth) := by
  unfold_word_group_envelope
  resource_polynomial

theorem uniform_mono {n m s K i b N M t T I B : ℕ}
    (hn : n ≤ N) (hm : m ≤ M) (hs : s ≤ t) (hK : K ≤ T) (hi : i ≤ I) (hb : b ≤ B) :
    BinaryWordGroupEmissionLifetime.uniformEnvelope n m s K i b ≤
      BinaryWordGroupEmissionLifetime.uniformEnvelope N M t T I B := by
  unfold_word_group_envelope
  unfold expressionHeightBudget
  gcongr

theorem mixed_mono {n s K i b N t T I B : ℕ}
    (hn : n ≤ N) (hs : s ≤ t) (hK : K ≤ T) (hi : i ≤ I) (hb : b ≤ B) :
    BinaryWordGroupEmissionLifetime.mixedEnvelope n s K i b ≤
      BinaryWordGroupEmissionLifetime.mixedEnvelope N t T I B := by
  unfold_word_group_envelope
  unfold expressionHeightBudget
  gcongr

theorem uniform_envelope_polynomial : ∃ C d : ℕ,∀ n m s K i b,
    BinaryWordGroupEmissionLifetime.uniformEnvelope n m s K i b ≤ C * (n + m + s + K + i + b + 2)^d := by
  rcases uniform_diagonal_polynomial with ⟨C,d,hBound⟩
  refine ⟨C,d,?_⟩
  intro n m s K i b
  let T := n + m + s + K + i + b
  have hMono : BinaryWordGroupEmissionLifetime.uniformEnvelope n m s K i b ≤
      BinaryWordGroupEmissionLifetime.uniformEnvelope T T T T T T := uniform_mono
    (by dsimp [T]; omega) (by dsimp [T]; omega) (by dsimp [T]; omega)
    (by dsimp [T]; omega) (by dsimp [T]; omega) (by dsimp [T]; omega)
  have h := hBound ⟨0,T,0,0,0⟩
  have hSize : inputSize ⟨0,T,0,0,0⟩ + 1 = T + 2 := by simp [inputSize,binaryWordWidth]
  rw [hSize] at h
  exact hMono.trans h

theorem mixed_envelope_polynomial : ∃ C d : ℕ,∀ n s K i b,
    BinaryWordGroupEmissionLifetime.mixedEnvelope n s K i b ≤ C * (n + s + K + i + b + 2)^d := by
  rcases mixed_diagonal_polynomial with ⟨C,d,hBound⟩
  refine ⟨C,d,?_⟩
  intro n s K i b
  let T := n + s + K + i + b
  have hMono : BinaryWordGroupEmissionLifetime.mixedEnvelope n s K i b ≤
      BinaryWordGroupEmissionLifetime.mixedEnvelope T T T T T := mixed_mono
    (by dsimp [T]; omega) (by dsimp [T]; omega) (by dsimp [T]; omega)
    (by dsimp [T]; omega) (by dsimp [T]; omega)
  have h := hBound ⟨0,T,0,0,0⟩
  have hSize : inputSize ⟨0,T,0,0,0⟩ + 1 = T + 2 := by simp [inputSize,binaryWordWidth]
  rw [hSize] at h
  exact hMono.trans h

open BinaryRationalNormalization BinaryRationalEncoding BinaryGroupInputs BinaryGroupSamplers BinaryCachedThreeDescriptorWork in
theorem uniform_source_usage : ∃ C d : ℕ,∀ {n m : ℕ} (store : BinarySeedLookupTree.Store)
    (input : UniformInput m) (hC : input.Canonical) (hAd : UniformAdmissible input) (hm : m = 2 ∨ m = 3)
    (routes : FixedArrayTable n (BinaryGroupRoutes.Route m)),(∀ j,CanonicalWord (routes.read j).2) →
    ∀ s,3 ≤ s → UniformHeights input s →
    (∀ j,RationalHeight (value (routes.read j).2) (expressionHeightBudget s 1)) →
    ∀ (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value),
    usage (BinaryWordGroupEmissionLifetime.uniformRun store input hC hAd hm routes K scalar pc hp).2 ≤
      C * (n + m + s + K + store.width + store.cap.value + 2)^d := by
  rcases uniform_envelope_polynomial with ⟨C,d,hBound⟩
  refine ⟨C,d,?_⟩
  intro n m store input hC hAd hm routes hRoutesC s hs hHeight hRoutes K scalar pc hp
  exact (BinaryWordGroupEmissionLifetime.uniformRun_usage store input hC hAd hm routes hRoutesC s hs
    hHeight hRoutes K scalar pc hp).trans (hBound n m s K store.width store.cap.value)

open BinaryRationalNormalization BinaryRationalEncoding BinaryGroupInputs BinaryGroupSamplers BinaryCachedThreeDescriptorWork in
theorem mixed_source_usage : ∃ C d : ℕ,∀ {n : ℕ} (store : BinarySeedLookupTree.Store)
    (input : MixedInput 2) (hC : input.Canonical) (hAd : MixedAdmissible input)
    (routes : FixedArrayTable n (BinaryGroupRoutes.Route 2)) (pivot : Fin n),(∀ j,CanonicalWord (routes.read j).2) →
    ∀ s,3 ≤ s → MixedHeights input s →
    (∀ j,RationalHeight (value (routes.read j).2) (expressionHeightBudget s 1)) →
    ∀ (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value),
    usage (BinaryWordGroupEmissionLifetime.mixedTwoRun store input hC hAd routes pivot K scalar pc hp).2 ≤
      C * (n + s + K + store.width + store.cap.value + 2)^d := by
  rcases mixed_envelope_polynomial with ⟨C,d,hBound⟩
  refine ⟨C,d,?_⟩
  intro n store input hC hAd routes pivot hRoutesC s hs hHeight hRoutes K scalar pc hp
  exact (BinaryWordGroupEmissionLifetime.mixedTwoRun_usage store input hC hAd routes pivot hRoutesC s hs
    hHeight hRoutes K scalar pc hp).trans (hBound n s K store.width store.cap.value)

end Blotto.BinaryWordGroupLifetimePolynomial
