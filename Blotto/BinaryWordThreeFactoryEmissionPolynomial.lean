import Blotto.BinaryScalarTape
import Blotto.BinaryWordThreeFactoryEmissionLifetime

/-! Original regular-three environment and cached route heights supply
polynomial complete factory/draw/emission source usage and every prefix. -/
namespace Blotto.BinaryWordThreeFactoryEmissionPolynomial
open BinaryPRGHeapResourcePolynomial BinaryPRGHeapTraceUsage BinarySeedPreparationSpace
set_option maxHeartbeats 3000000

macro "unfold_word_three_emission_envelope" : tactic => `(tactic|
  simp only [BinaryWordThreeFactoryEmissionLifetime.uniformEnvelope,BinaryWordThreeFactoryEmissionLifetime.mixedEnvelope,
    BinaryQuadraticThreeFactoryLifetime.bound,BinaryQuadraticThreeFactoryLifetime.frames,
    BinaryQuadraticThreeFactoryLifetime.expressionBound,BinaryQuadraticThreeFactoryLifetime.expressionFrames])

theorem uniform_polynomial : NaturalPolynomialEnvelope inputSize (fun p =>
    BinaryWordThreeFactoryEmissionLifetime.uniformEnvelope p.count p.wordWidth p.wordWidth p.seedWidth p.seedCap) := by
  unfold_word_three_emission_envelope
  unfold_word_terminal_envelope
  resource_polynomial

theorem mixed_polynomial : NaturalPolynomialEnvelope inputSize (fun p =>
    BinaryWordThreeFactoryEmissionLifetime.mixedEnvelope p.count p.wordWidth p.wordWidth p.seedWidth p.seedCap) := by
  unfold_word_three_emission_envelope
  unfold_word_terminal_envelope
  resource_polynomial

theorem uniform_mono {n s K i b N t T I B : ℕ}
    (hn : n ≤ N) (hs : s ≤ t) (hK : K ≤ T) (hi : i ≤ I) (hb : b ≤ B) :
    BinaryWordThreeFactoryEmissionLifetime.uniformEnvelope n s K i b ≤
      BinaryWordThreeFactoryEmissionLifetime.uniformEnvelope N t T I B := by
  unfold_word_three_emission_envelope
  unfold_word_terminal_envelope
  unfold expressionHeightBudget
  gcongr

theorem mixed_mono {n s K i b N t T I B : ℕ}
    (hn : n ≤ N) (hs : s ≤ t) (hK : K ≤ T) (hi : i ≤ I) (hb : b ≤ B) :
    BinaryWordThreeFactoryEmissionLifetime.mixedEnvelope n s K i b ≤
      BinaryWordThreeFactoryEmissionLifetime.mixedEnvelope N t T I B := by
  unfold_word_three_emission_envelope
  unfold_word_terminal_envelope
  unfold expressionHeightBudget
  gcongr

theorem uniform_envelope : ∃ C d : ℕ,∀ n s K i b,
    BinaryWordThreeFactoryEmissionLifetime.uniformEnvelope n s K i b ≤ C * (n + s + K + i + b + 2)^d := by
  rcases uniform_polynomial with ⟨C,d,hBound⟩
  refine ⟨C,d,?_⟩
  intro n s K i b
  have hMono := uniform_mono (n := n) (i := i) (b := b) le_rfl (show s ≤ s + K by omega) (show K ≤ s + K by omega) le_rfl le_rfl
  have h := hBound ⟨n,s + K,0,i,b⟩
  have hSize : inputSize ⟨n,s + K,0,i,b⟩ + 1 = n + s + K + i + b + 2 := by
    simp [inputSize,binaryWordWidth]
    omega
  rw [hSize] at h
  exact hMono.trans h

theorem mixed_envelope : ∃ C d : ℕ,∀ n s K i b,
    BinaryWordThreeFactoryEmissionLifetime.mixedEnvelope n s K i b ≤ C * (n + s + K + i + b + 2)^d := by
  rcases mixed_polynomial with ⟨C,d,hBound⟩
  refine ⟨C,d,?_⟩
  intro n s K i b
  have hMono := mixed_mono (n := n) (i := i) (b := b) le_rfl (show s ≤ s + K by omega) (show K ≤ s + K by omega) le_rfl le_rfl
  have h := hBound ⟨n,s + K,0,i,b⟩
  have hSize : inputSize ⟨n,s + K,0,i,b⟩ + 1 = n + s + K + i + b + 2 := by
    simp [inputSize,binaryWordWidth]
    omega
  rw [hSize] at h
  exact hMono.trans h

open BinaryRationalNormalization BinaryRationalEncoding BinarySyntaxUniformWork BinaryThreeDescriptorCompiler in
theorem uniform_all_prefix {n : ℕ} (store : BinarySeedLookupTree.Store) (env : FixedArrayTable 4 SignedWord)
    (hC : ∀ j,CanonicalWord (env.read j)) (hN : ∀ slot,0 ≤ value ((descriptor env).weight.read slot))
    (source : RationalSegmentLottery 3 9) (hR : (descriptor env).Refines source)
    (routes : FixedArrayTable n (BinaryGroupRoutes.Route 3)) (hRC : ∀ j,CanonicalWord (routes.read j).2)
    (s : ℕ) (hs : 3 ≤ s) (hEnv : EnvHeight env s) (hRoutes : ∀ j,RationalHeight (value (routes.read j).2) s)
    (fallback : Fin 9) (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value)
    (borrowed steps : ℕ) :
    retainedHeap borrowed (BinaryWordThreeFactoryEmissionLifetime.uniformRun store env hC hN routes fallback K scalar pc hp).2 steps ≤
        borrowed + BinaryWordThreeFactoryEmissionLifetime.uniformEnvelope n s K store.width store.cap.value ∧
      framePeak ((BinaryWordThreeFactoryEmissionLifetime.uniformRun store env hC hN routes fallback K scalar pc hp).2.take steps) ≤
        BinaryWordThreeFactoryEmissionLifetime.uniformEnvelope n s K store.width store.cap.value :=
  BinaryPRGHeapTraceUsage.all_prefix _ _
    (BinaryWordThreeFactoryEmissionLifetime.uniformRun_usage store env hC hN source hR routes hRC s hs hEnv hRoutes fallback K scalar pc hp) borrowed steps

open BinaryRationalNormalization BinaryRationalEncoding BinarySyntaxUniformWork BinaryThreeDescriptorCompiler in
theorem mixed_all_prefix {n : ℕ} (store : BinarySeedLookupTree.Store) (env : FixedArrayTable 4 SignedWord)
    (hC : ∀ j,CanonicalWord (env.read j)) (hN : ∀ slot,0 ≤ value ((descriptor env).weight.read slot))
    (source : RationalSegmentLottery 3 9) (hR : (descriptor env).Refines source)
    (routes : FixedArrayTable n (BinaryGroupRoutes.Route 2)) (pivot : Fin n) (hRC : ∀ j,CanonicalWord (routes.read j).2)
    (s : ℕ) (hs : 3 ≤ s) (hEnv : EnvHeight env s) (hRoutes : ∀ j,RationalHeight (value (routes.read j).2) s)
    (fallback : Fin 9) (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value)
    (borrowed steps : ℕ) :
    retainedHeap borrowed (BinaryWordThreeFactoryEmissionLifetime.mixedRun store env hC hN routes pivot fallback K scalar pc hp).2 steps ≤
        borrowed + BinaryWordThreeFactoryEmissionLifetime.mixedEnvelope n s K store.width store.cap.value ∧
      framePeak ((BinaryWordThreeFactoryEmissionLifetime.mixedRun store env hC hN routes pivot fallback K scalar pc hp).2.take steps) ≤
        BinaryWordThreeFactoryEmissionLifetime.mixedEnvelope n s K store.width store.cap.value :=
  BinaryPRGHeapTraceUsage.all_prefix _ _
    (BinaryWordThreeFactoryEmissionLifetime.mixedRun_usage store env hC hN source hR routes pivot hRC s hs hEnv hRoutes fallback K scalar pc hp) borrowed steps

end Blotto.BinaryWordThreeFactoryEmissionPolynomial
