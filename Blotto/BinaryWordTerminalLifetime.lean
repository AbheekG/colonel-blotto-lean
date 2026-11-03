import Blotto.BinaryScalarTape
import Blotto.BinaryWordSmallTerminalLifetime
import Blotto.BinaryWordMixedThreeTerminalLifetime

/-! Complete cached terminal dispatch, including mixed-three. Actual retained
count/pivot/totals/routes choose the uniform, mixed-two or mixed-three producer;
there is no SmallBranch restriction and no replay of cache preparation. -/
namespace Blotto.BinaryWordTerminalLifetime
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryCachedTerminalPreparation BinaryCachedThreeDescriptorWork
set_option maxHeartbeats 2000000

def runWithTrace {n : ℕ} (store : BinarySeedLookupTree.Store) {input : BinaryTerminalGrouping.Input n}
    (prepared : Prepared input) (hC : input.Canonical) (hAd : BinaryTerminalPromises.Admissible input)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    BinaryPRGWordControllerTerminal.Result store n × Trace :=
  match hPivot : prepared.pivot with
  | none =>
      let drawn := BinaryWordUniformTerminalLifetime.runWithTrace store prepared hC hAd hPivot K scalar pc hp
      (drawn.1,wrap 24 2 [drawn.2])
  | some selected =>
      if hTwo : prepared.count = 2 then
        let drawn := BinaryWordMixedTwoTerminalLifetime.runWithTrace store prepared hC hAd
          hTwo selected hPivot K scalar pc hp
        (drawn.1,wrap 24 2 [drawn.2])
      else
        have hThree : prepared.count = 3 := (prepared.count_bound hC hAd).resolve_left hTwo
        let drawn := BinaryWordMixedThreeTerminalLifetime.runWithTrace store prepared hC hAd
          hThree selected hPivot K outer scalar pc hp
        (drawn.1,wrap 24 2 [drawn.2])

theorem runWithTrace_erasure {n : ℕ} (store : BinarySeedLookupTree.Store) {input : BinaryTerminalGrouping.Input n}
    (prepared : Prepared input) (hC : input.Canonical) (hAd : BinaryTerminalPromises.Admissible input)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (runWithTrace store prepared hC hAd K outer scalar pc hp).1 =
      BinaryPRGWordControllerTerminal.runPrepared store prepared hC hAd K outer scalar pc hp := by
  unfold runWithTrace
  dsimp only
  split
  · rename_i hPivot
    exact BinaryWordUniformTerminalLifetime.runWithTrace_erasure store prepared hC hAd hPivot K outer scalar pc hp
  · rename_i selected hPivot
    split
    · rename_i hTwo
      exact BinaryWordMixedTwoTerminalLifetime.runWithTrace_erasure store prepared hC hAd
        hTwo selected hPivot K outer scalar pc hp
    · rename_i hTwo
      exact BinaryWordMixedThreeTerminalLifetime.runWithTrace_erasure store prepared hC hAd
        ((prepared.count_bound hC hAd).resolve_left hTwo) selected hPivot K outer scalar pc hp

theorem runWithTrace_position {n : ℕ} (store : BinarySeedLookupTree.Store) {input : BinaryTerminalGrouping.Input n}
    (prepared : Prepared input) (hC : input.Canonical) (hAd : BinaryTerminalPromises.Admissible input)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    pc.value ≤ (runWithTrace store prepared hC hAd K outer scalar pc hp).1.2.value ∧
      (runWithTrace store prepared hC hAd K outer scalar pc hp).1.2.value ≤ store.cap.value := by
  rw [runWithTrace_erasure]
  exact BinaryPRGWordControllerTerminal.runPrepared_position store prepared hC hAd K outer scalar pc hp

def envelope (n s K indexWidth seedCap remaining : ℕ) : ℕ :=
  BinaryWordUniformTerminalLifetime.envelope n s K indexWidth seedCap +
    BinaryWordMixedTwoTerminalLifetime.envelope n s K indexWidth seedCap +
    BinaryWordMixedThreeTerminalLifetime.envelope n s K indexWidth seedCap remaining + 128

theorem runWithTrace_usage {n : ℕ} (store : BinarySeedLookupTree.Store) {input : BinaryTerminalGrouping.Input n}
    (prepared : Prepared input) (hC : input.Canonical) (hAd : BinaryTerminalPromises.Admissible input)
    (s : ℕ) (hs : 3 ≤ s) (hUniform : UniformHeights prepared.uniform s)
    (hMixed : ∀ selected,prepared.pivot = some selected → MixedHeights prepared.mixed s)
    (hRoutes : ∀ j,RationalHeight (value (prepared.routes.read j).2) (expressionHeightBudget s 1))
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    usage (runWithTrace store prepared hC hAd K outer scalar pc hp).2 ≤
      envelope n s K store.width store.cap.value (store.cap.value-pc.value) := by
  unfold runWithTrace
  dsimp only
  split
  · rename_i hPivot
    have h := BinaryWordUniformTerminalLifetime.runWithTrace_usage store prepared hC hAd hPivot
      s hs hUniform hRoutes K scalar pc hp
    have hw := wrap_usage 24 2
      [(BinaryWordUniformTerminalLifetime.runWithTrace store prepared hC hAd hPivot K scalar pc hp).2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    dsimp only
    unfold envelope
    omega
  · rename_i selected hPivot
    split
    · rename_i hTwo
      have h := BinaryWordMixedTwoTerminalLifetime.runWithTrace_usage store prepared hC hAd hTwo selected hPivot
        s hs (hMixed selected hPivot) hRoutes K scalar pc hp
      have hw := wrap_usage 24 2
        [(BinaryWordMixedTwoTerminalLifetime.runWithTrace store prepared hC hAd hTwo selected hPivot K scalar pc hp).2]
      simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
      dsimp only
      unfold envelope
      omega
    · rename_i hTwo
      let hThree := (prepared.count_bound hC hAd).resolve_left hTwo
      have h := BinaryWordMixedThreeTerminalLifetime.runWithTrace_usage store prepared hC hAd hThree selected hPivot
        s hs (hMixed selected hPivot) hRoutes K outer scalar pc hp
      have hw := wrap_usage 24 2
        [(BinaryWordMixedThreeTerminalLifetime.runWithTrace store prepared hC hAd hThree selected hPivot K outer scalar pc hp).2]
      simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
      dsimp only
      unfold envelope
      omega

theorem all_prefix {n : ℕ} (store : BinarySeedLookupTree.Store) {input : BinaryTerminalGrouping.Input n}
    (prepared : Prepared input) (hC : input.Canonical) (hAd : BinaryTerminalPromises.Admissible input)
    (s : ℕ) (hs : 3 ≤ s) (hUniform : UniformHeights prepared.uniform s)
    (hMixed : ∀ selected,prepared.pivot = some selected → MixedHeights prepared.mixed s)
    (hRoutes : ∀ j,RationalHeight (value (prepared.routes.read j).2) (expressionHeightBudget s 1))
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value)
    (borrowed steps : ℕ) :
    retainedHeap borrowed (runWithTrace store prepared hC hAd K outer scalar pc hp).2 steps ≤
      borrowed + envelope n s K store.width store.cap.value (store.cap.value-pc.value) ∧
    framePeak ((runWithTrace store prepared hC hAd K outer scalar pc hp).2.take steps) ≤
      envelope n s K store.width store.cap.value (store.cap.value-pc.value) :=
  BinaryPRGHeapTraceUsage.all_prefix _ _
    (runWithTrace_usage store prepared hC hAd s hs hUniform hMixed hRoutes K outer scalar pc hp) borrowed steps

theorem envelope_remaining_mono (n s K i b r R : ℕ) (h : r ≤ R) :
    envelope n s K i b r ≤ envelope n s K i b R := by
  simp only [envelope,BinaryWordMixedThreeTerminalLifetime.envelope,
    BinaryWordMixedThreeLifetime.envelope,BinaryWordMixedThreeLifetime.drawEnvelope,
    BinaryFourRestoredLifetime.envelope,BinaryFourOrderedLifetime.envelope,BinaryFourSmallLifetime.envelope]
  unfold BinaryFourSmallCoinLifetime.envelope BinaryWordCoinLifetime.sampleBound
  gcongr

end Blotto.BinaryWordTerminalLifetime
