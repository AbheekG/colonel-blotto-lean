import Blotto.BinaryScalarTape
import Blotto.BinaryWordUniformTerminalLifetime
import Blotto.BinaryWordMixedTwoTerminalLifetime

/-! Actual terminal dispatch for both uniform group counts and mixed-two.
The named SmallBranch condition excludes precisely the mixed-three/four-variable
continuation, which remains open in this lifetime lane. -/
namespace Blotto.BinaryWordSmallTerminalLifetime
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryCachedTerminalPreparation BinaryCachedThreeDescriptorWork
set_option maxHeartbeats 2000000

def SmallBranch {n : ℕ} {input : BinaryTerminalGrouping.Input n} (prepared : Prepared input) : Prop :=
  ∀ selected,prepared.pivot = some selected → prepared.count = 2

def runWithTrace {n : ℕ} (store : BinarySeedLookupTree.Store) {input : BinaryTerminalGrouping.Input n}
    (prepared : Prepared input) (hC : input.Canonical) (hAd : BinaryTerminalPromises.Admissible input)
    (hSmall : SmallBranch prepared) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    BinaryPRGWordControllerTerminal.Result store n × Trace :=
  match hs : prepared.pivot with
  | none =>
      let drawn := BinaryWordUniformTerminalLifetime.runWithTrace store prepared hC hAd hs K scalar pc hp
      (drawn.1,wrap 16 2 [drawn.2])
  | some selected =>
      let drawn := BinaryWordMixedTwoTerminalLifetime.runWithTrace store prepared hC hAd (hSmall selected hs) selected hs K scalar pc hp
      (drawn.1,wrap 16 2 [drawn.2])

theorem runWithTrace_erasure {n : ℕ} (store : BinarySeedLookupTree.Store) {input : BinaryTerminalGrouping.Input n}
    (prepared : Prepared input) (hC : input.Canonical) (hAd : BinaryTerminalPromises.Admissible input)
    (hSmall : SmallBranch prepared) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (runWithTrace store prepared hC hAd hSmall K scalar pc hp).1 =
      BinaryPRGWordControllerTerminal.runPrepared store prepared hC hAd K outer scalar pc hp := by
  unfold runWithTrace
  dsimp only
  split
  · rename_i hPivot
    exact BinaryWordUniformTerminalLifetime.runWithTrace_erasure store prepared hC hAd hPivot K outer scalar pc hp
  · rename_i selected hPivot
    exact BinaryWordMixedTwoTerminalLifetime.runWithTrace_erasure store prepared hC hAd
      (hSmall selected hPivot) selected hPivot K outer scalar pc hp

def envelope (n s K indexWidth seedCap : ℕ) : ℕ :=
  BinaryWordUniformTerminalLifetime.envelope n s K indexWidth seedCap +
    BinaryWordMixedTwoTerminalLifetime.envelope n s K indexWidth seedCap + 32

theorem runWithTrace_usage {n : ℕ} (store : BinarySeedLookupTree.Store) {input : BinaryTerminalGrouping.Input n}
    (prepared : Prepared input) (hC : input.Canonical) (hAd : BinaryTerminalPromises.Admissible input)
    (hSmall : SmallBranch prepared) (s : ℕ) (hs : 3 ≤ s) (hUniform : UniformHeights prepared.uniform s)
    (hMixed : ∀ selected,prepared.pivot = some selected → MixedHeights prepared.mixed s)
    (hRoutes : ∀ j,RationalHeight (value (prepared.routes.read j).2) (expressionHeightBudget s 1))
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    usage (runWithTrace store prepared hC hAd hSmall K scalar pc hp).2 ≤ envelope n s K store.width store.cap.value := by
  unfold runWithTrace
  dsimp only
  split
  · rename_i hPivot
    have h := BinaryWordUniformTerminalLifetime.runWithTrace_usage store prepared hC hAd hPivot s hs hUniform hRoutes K scalar pc hp
    have hw := wrap_usage 16 2 [(BinaryWordUniformTerminalLifetime.runWithTrace store prepared hC hAd hPivot K scalar pc hp).2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    dsimp only
    unfold envelope
    omega
  · rename_i selected hPivot
    have h := BinaryWordMixedTwoTerminalLifetime.runWithTrace_usage store prepared hC hAd (hSmall selected hPivot) selected hPivot
      s hs (hMixed selected hPivot) hRoutes K scalar pc hp
    have hw := wrap_usage 16 2 [(BinaryWordMixedTwoTerminalLifetime.runWithTrace store prepared hC hAd
      (hSmall selected hPivot) selected hPivot K scalar pc hp).2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    dsimp only
    unfold envelope
    omega

theorem diagonal_polynomial : NaturalPolynomialEnvelope BinaryPRGHeapResourcePolynomial.inputSize
    (fun p => envelope p.wordWidth p.wordWidth p.wordWidth p.wordWidth p.wordWidth) := by
  simp only [envelope,BinaryWordUniformTerminalLifetime.envelope,BinaryWordMixedTwoTerminalLifetime.envelope]
  unfold_word_group_envelope
  resource_polynomial

theorem envelope_mono {n s K i b N t T I B : ℕ} (hn : n ≤ N) (hs : s ≤ t) (hK : K ≤ T) (hi : i ≤ I) (hb : b ≤ B) :
    envelope n s K i b ≤ envelope N t T I B := by
  simp only [envelope,BinaryWordUniformTerminalLifetime.envelope,BinaryWordMixedTwoTerminalLifetime.envelope]
  unfold_word_group_envelope
  unfold expressionHeightBudget
  gcongr

theorem envelope_polynomial : ∃ C d : ℕ,∀ n s K i b,envelope n s K i b ≤ C * (n + s + K + i + b + 2)^d := by
  rcases diagonal_polynomial with ⟨C,d,hBound⟩
  refine ⟨C,d,?_⟩
  intro n s K i b
  let T := n + s + K + i + b
  have hMono : envelope n s K i b ≤ envelope T T T T T := envelope_mono
    (by dsimp [T]; omega) (by dsimp [T]; omega) (by dsimp [T]; omega) (by dsimp [T]; omega) (by dsimp [T]; omega)
  have h := hBound ⟨0,T,0,0,0⟩
  have hSize : BinaryPRGHeapResourcePolynomial.inputSize ⟨0,T,0,0,0⟩ + 1 = T + 2 := by
    simp [BinaryPRGHeapResourcePolynomial.inputSize,binaryWordWidth]
  rw [hSize] at h
  exact hMono.trans h

end Blotto.BinaryWordSmallTerminalLifetime
