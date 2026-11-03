import Blotto.BinaryScalarTape
import Blotto.BinaryWordSegmentEmissionBound
import Blotto.BinaryPRGHeapResourcePolynomial

/-! Uniform polynomial growth of complete Boolean-PC segment-to-route traces.
These count retained source cells and activations, not host allocator space
or sharp reclaimed-space/fast-arithmetic exponents. -/
namespace Blotto.BinaryWordTerminalLifetimePolynomial
open BinaryPRGHeapResourcePolynomial BinaryPRGHeapTraceUsage
set_option maxHeartbeats 3000000

macro "unfold_word_terminal_envelope" : tactic => `(tactic|
  simp only [BinaryWordSegmentEmissionBound.uniformEnvelope,BinaryWordSegmentEmissionBound.mixedEnvelope,
    BinaryWordSegmentLifetimeBound.envelope,BinaryWordSegmentLifetimeBound.selectionEnvelope,
    BinaryWordSegmentLifetimeBound.sourceStepEnvelope,BinaryWordCategoricalLifetimeBound.coinEnvelope,
    BinaryWordCoinLifetime.sampleBound,BinaryWordCoinLifetime.localBound,
    BinaryQuadraticPointLifetime.bound,BinaryQuadraticPointLifetime.frames,
    BinaryQuadraticPointLifetime.expressionBound,BinaryQuadraticPointLifetime.expressionFrames,
    BinaryPhysicalPointLifetime.bound,BinaryPhysicalPointLifetime.wordCap,
    BinaryPhysicalInterpolationRun.bound,BinaryPhysicalInterpolationRun.stepEnvelope,
    BinaryPhysicalInterpolation.bound,BinaryPhysicalOutputLifetime.preparationBound,
    BinaryPhysicalOutputLifetime.readEnvelope,BinaryPhysicalOutputLifetime.heapCap,BinaryPhysicalOutputLifetime.slotsCap,
    BinaryReferenceVector.readBound,BinaryPRGWordStoreHeapMachine.readBound,BinaryPRGWordStoreHeapMachine.skipBound,
    BinaryQuadraticSyntaxLifetime.bound,BinaryQuadraticSyntaxLifetime.frames,
    BinaryQuadraticExpressionLifetime.stepBound,BinaryQuadraticExpressionLifetime.frameBound,
    BinaryGroupEmissionLifetimeBound.envelope,BinaryGroupEmissionLifetimeBound.mixedEnvelope,
    BinaryLifetimeUsage.opcodeEnvelope,BinaryWordSegmentResultHeight.rowHeight,
    BinaryQuadraticLifetime.opcodeBound,BinaryQuadraticLifetime.opcodeFrames])

theorem uniform_diagonal_polynomial : NaturalPolynomialEnvelope inputSize (fun p =>
    BinaryWordSegmentEmissionBound.uniformEnvelope p.wordWidth p.wordWidth p.wordWidth p.wordWidth p.wordWidth p.wordWidth p.wordWidth) := by
  unfold_word_terminal_envelope
  resource_polynomial

theorem mixed_diagonal_polynomial : NaturalPolynomialEnvelope inputSize (fun p =>
    BinaryWordSegmentEmissionBound.mixedEnvelope p.wordWidth p.wordWidth p.wordWidth p.wordWidth p.wordWidth p.wordWidth p.wordWidth) := by
  unfold_word_terminal_envelope
  resource_polynomial

theorem uniform_mono {n m k s K i b N M L t T I B : ℕ}
    (hn : n ≤ N) (hm : m ≤ M) (hk : k ≤ L) (hs : s ≤ t) (hK : K ≤ T) (hi : i ≤ I) (hb : b ≤ B) :
    BinaryWordSegmentEmissionBound.uniformEnvelope n m k s K i b ≤
      BinaryWordSegmentEmissionBound.uniformEnvelope N M L t T I B := by
  unfold_word_terminal_envelope
  unfold expressionHeightBudget
  gcongr

theorem mixed_mono {n m k s K i b N M L t T I B : ℕ}
    (hn : n ≤ N) (hm : m ≤ M) (hk : k ≤ L) (hs : s ≤ t) (hK : K ≤ T) (hi : i ≤ I) (hb : b ≤ B) :
    BinaryWordSegmentEmissionBound.mixedEnvelope n m k s K i b ≤
      BinaryWordSegmentEmissionBound.mixedEnvelope N M L t T I B := by
  unfold_word_terminal_envelope
  unfold expressionHeightBudget
  gcongr

theorem uniform_envelope_polynomial : ∃ C d : ℕ,∀ n m k s K i b,
    BinaryWordSegmentEmissionBound.uniformEnvelope n m k s K i b ≤ C * (n + m + k + s + K + i + b + 2)^d := by
  rcases uniform_diagonal_polynomial with ⟨C,d,hBound⟩
  refine ⟨C,d,?_⟩
  intro n m k s K i b
  let T := n + m + k + s + K + i + b
  have hMono : BinaryWordSegmentEmissionBound.uniformEnvelope n m k s K i b ≤
      BinaryWordSegmentEmissionBound.uniformEnvelope T T T T T T T := uniform_mono
    (by dsimp [T]; omega) (by dsimp [T]; omega) (by dsimp [T]; omega) (by dsimp [T]; omega)
    (by dsimp [T]; omega) (by dsimp [T]; omega) (by dsimp [T]; omega)
  have h := hBound ⟨0,T,0,0,0⟩
  have hSize : inputSize ⟨0,T,0,0,0⟩ + 1 = T + 2 := by simp [inputSize,binaryWordWidth]
  rw [hSize] at h
  exact hMono.trans h

theorem mixed_envelope_polynomial : ∃ C d : ℕ,∀ n m k s K i b,
    BinaryWordSegmentEmissionBound.mixedEnvelope n m k s K i b ≤ C * (n + m + k + s + K + i + b + 2)^d := by
  rcases mixed_diagonal_polynomial with ⟨C,d,hBound⟩
  refine ⟨C,d,?_⟩
  intro n m k s K i b
  let T := n + m + k + s + K + i + b
  have hMono : BinaryWordSegmentEmissionBound.mixedEnvelope n m k s K i b ≤
      BinaryWordSegmentEmissionBound.mixedEnvelope T T T T T T T := mixed_mono
    (by dsimp [T]; omega) (by dsimp [T]; omega) (by dsimp [T]; omega) (by dsimp [T]; omega)
    (by dsimp [T]; omega) (by dsimp [T]; omega) (by dsimp [T]; omega)
  have h := hBound ⟨0,T,0,0,0⟩
  have hSize : inputSize ⟨0,T,0,0,0⟩ + 1 = T + 2 := by simp [inputSize,binaryWordWidth]
  rw [hSize] at h
  exact hMono.trans h

open BinaryRationalNormalization BinaryRationalEncoding BinaryStoredSegmentProgram in
theorem uniform_source_usage : ∃ C d : ℕ,∀ {n m k : ℕ} (store : BinarySeedLookupTree.Store)
    (prepared : Prepared m k) (fallback : Fin k) (source : RationalSegmentLottery m k),prepared.table.Refines source →
    ∀ (routes : FixedArrayTable n (BinaryGroupRoutes.Route m)),(∀ j,CanonicalWord (routes.read j).2) →
    ∀ s,3 ≤ s → (∀ j,RationalHeight (value (routes.read j).2) s) →
    (∀ slot,RationalHeight (source.weight slot) s) →
    (∀ slot j,RationalHeight (source.P slot j) s ∧ RationalHeight (source.Q slot j) s) →
    ∀ (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value),
    usage (BinaryWordSegmentEmissionLifetime.uniformRun store prepared fallback routes K scalar pc hp).2 ≤
      C * (n + m + k + s + K + store.width + store.cap.value + 2)^d := by
  rcases uniform_envelope_polynomial with ⟨C,d,hBound⟩
  refine ⟨C,d,?_⟩
  intro n m k store prepared fallback source hR routes hC s hs hRoutes hWeight hEndpoints K scalar pc hp
  exact (BinaryWordSegmentEmissionBound.uniformRun_usage store prepared fallback source hR routes hC s hs
    hRoutes hWeight hEndpoints K scalar pc hp).trans (hBound n m k s K store.width store.cap.value)

open BinaryRationalNormalization BinaryRationalEncoding BinaryStoredSegmentProgram in
theorem mixed_source_usage : ∃ C d : ℕ,∀ {n m k : ℕ} (store : BinarySeedLookupTree.Store)
    (prepared : Prepared (m + 1) k) (fallback : Fin k) (source : RationalSegmentLottery (m + 1) k),prepared.table.Refines source →
    ∀ (routes : FixedArrayTable n (BinaryGroupRoutes.Route m)) (pivot : Fin n),(∀ j,CanonicalWord (routes.read j).2) →
    ∀ s,3 ≤ s → (∀ j,RationalHeight (value (routes.read j).2) s) →
    (∀ slot,RationalHeight (source.weight slot) s) →
    (∀ slot j,RationalHeight (source.P slot j) s ∧ RationalHeight (source.Q slot j) s) →
    ∀ (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value),
    usage (BinaryWordSegmentEmissionLifetime.mixedRun store prepared fallback routes pivot K scalar pc hp).2 ≤
      C * (n + m + k + s + K + store.width + store.cap.value + 2)^d := by
  rcases mixed_envelope_polynomial with ⟨C,d,hBound⟩
  refine ⟨C,d,?_⟩
  intro n m k store prepared fallback source hR routes pivot hC s hs hRoutes hWeight hEndpoints K scalar pc hp
  exact (BinaryWordSegmentEmissionBound.mixedRun_usage store prepared fallback source hR routes pivot hC s hs
    hRoutes hWeight hEndpoints K scalar pc hp).trans (hBound n m k s K store.width store.cap.value)

end Blotto.BinaryWordTerminalLifetimePolynomial
