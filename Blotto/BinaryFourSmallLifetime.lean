import Blotto.BinaryScalarTape
import Blotto.BinaryReflectedDrawLifetime
import Blotto.BinaryFourSmallUniformDrawLifetime
import Blotto.BinaryFourSmallCoinLifetime

/-! Complete small-root execution samples its root coin once and hands the
actual returned cursor to the selected uniform or physical reflected branch.
Root, resource and categorical exhaustion remain explicit. -/
namespace Blotto.BinaryFourSmallLifetime
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGHeapTraceUsage
set_option maxHeartbeats 2000000

def runWithTrace (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (hC : input.Canonical) (hAd : BinarySmallRootSample.Admissible input)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width)
    (hp : pc.value ≤ store.cap.value) : BinaryPRGWordControllerFour.Result store × Trace :=
  let root := BinaryFourSmallCoinLifetime.sampleWithTrace store input pc hp
  have hNext : root.1.2.value ≤ store.cap.value :=
    (BinaryFourSmallCoinLifetime.sampleWithTrace_position store input pc hp).2
  match root.1.1 with
  | none => ((none,root.1.2),wrap 24 2 [root.2])
  | some true =>
      let drawn := BinaryFourSmallUniformDrawLifetime.runWithTrace store input hC hAd K scalar root.1.2 hNext
      (drawn.1,wrap 32 2 [root.2,drawn.2])
  | some false =>
      let drawn := BinaryReflectedDrawLifetime.runWithTrace store input hC hAd K outer scalar root.1.2 hNext
      (drawn.1,wrap 32 2 [root.2,drawn.2])

theorem runWithTrace_erasure (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (hC : input.Canonical) (hAd : BinarySmallRootSample.Admissible input)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (runWithTrace store input hC hAd K outer scalar pc hp).1 =
      BinaryPRGWordControllerFour.smallRun store input hC hAd K outer scalar pc hp := by
  have hRoot := BinaryFourSmallCoinLifetime.sampleWithTrace_erasure store input pc hp
  have hCursor := congrArg Prod.snd hRoot
  cases h : (BinaryFourSmallCoinLifetime.sampleWithTrace store input pc hp).1.1 with
  | none =>
      have hOldNone := (congrArg Prod.fst hRoot).symm.trans h
      unfold runWithTrace BinaryPRGWordControllerFour.smallRun
      dsimp only
      simp only [h,hOldNone]
      exact congrArg (fun cursor => (none,cursor)) hCursor
  | some branch =>
      cases branch
      · have hOldFalse := (congrArg Prod.fst hRoot).symm.trans h
        unfold runWithTrace BinaryPRGWordControllerFour.smallRun
        dsimp only
        simp only [h,hOldFalse]
        rw [BinaryReflectedDrawLifetime.runWithTrace_erasure]
        simpa only [hCursor]
      · have hOldTrue := (congrArg Prod.fst hRoot).symm.trans h
        unfold runWithTrace BinaryPRGWordControllerFour.smallRun
        dsimp only
        simp only [h,hOldTrue]
        rw [BinaryFourSmallUniformDrawLifetime.runWithTrace_erasure]
        simpa only [hCursor]

theorem runWithTrace_position (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (hC : input.Canonical) (hAd : BinarySmallRootSample.Admissible input)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    pc.value ≤ (runWithTrace store input hC hAd K outer scalar pc hp).1.2.value ∧
      (runWithTrace store input hC hAd K outer scalar pc hp).1.2.value ≤ store.cap.value := by
  rw [runWithTrace_erasure]
  exact BinaryPRGWordControllerFour.smallRun_position store input hC hAd K outer scalar pc hp

def envelope (s K indexWidth seedCap remaining : ℕ) : ℕ :=
  BinaryFourSmallCoinLifetime.envelope s indexWidth remaining +
    BinaryFourSmallUniformDrawLifetime.envelope s K indexWidth seedCap +
    BinaryReflectedDrawLifetime.envelope s K indexWidth seedCap + 256

theorem runWithTrace_usage (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (source : RationalFourInput) (hC : input.Canonical) (hR : input.Refines source)
    (hCase : source.w < (1-source.p)*source.ell) (hAd : BinarySmallRootSample.Admissible input)
    (s : ℕ) (hs : 3 ≤ s) (hH : source.FieldsHeight s)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    usage (runWithTrace store input hC hAd K outer scalar pc hp).2 ≤
      envelope s K store.width store.cap.value (store.cap.value-pc.value) := by
  let root := BinaryFourSmallCoinLifetime.sampleWithTrace store input pc hp
  have hNext : root.1.2.value ≤ store.cap.value :=
    (BinaryFourSmallCoinLifetime.sampleWithTrace_position store input pc hp).2
  have hRoot := BinaryFourSmallCoinLifetime.sampleWithTrace_usage store input source hC hR s hH pc hp
  change usage root.2 ≤ _ at hRoot
  have hUniform := BinaryFourSmallUniformDrawLifetime.runWithTrace_usage store input source hC hR hCase hAd
    s hs hH K scalar root.1.2 hNext
  have hReflected := BinaryReflectedDrawLifetime.runWithTrace_usage store input source hC hR hCase hAd
    s (by omega) hH K outer scalar root.1.2 hNext
  unfold runWithTrace
  dsimp only
  split
  · have hw := wrap_usage 24 2 [root.2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change usage (wrap 24 2 [root.2]) ≤ _
    unfold envelope
    omega
  · have hw := wrap_usage 32 2 [root.2,
      (BinaryFourSmallUniformDrawLifetime.runWithTrace store input hC hAd K scalar root.1.2 hNext).2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change usage (wrap 32 2 [root.2,
      (BinaryFourSmallUniformDrawLifetime.runWithTrace store input hC hAd K scalar root.1.2 hNext).2]) ≤ _
    unfold envelope
    omega
  · have hw := wrap_usage 32 2 [root.2,
      (BinaryReflectedDrawLifetime.runWithTrace store input hC hAd K outer scalar root.1.2 hNext).2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change usage (wrap 32 2 [root.2,
      (BinaryReflectedDrawLifetime.runWithTrace store input hC hAd K outer scalar root.1.2 hNext).2]) ≤ _
    unfold envelope
    omega

theorem all_prefix (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (source : RationalFourInput) (hC : input.Canonical) (hR : input.Refines source)
    (hCase : source.w < (1-source.p)*source.ell) (hAd : BinarySmallRootSample.Admissible input)
    (s : ℕ) (hs : 3 ≤ s) (hH : source.FieldsHeight s)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value)
    (borrowed steps : ℕ) :
    retainedHeap borrowed (runWithTrace store input hC hAd K outer scalar pc hp).2 steps ≤
      borrowed + envelope s K store.width store.cap.value (store.cap.value-pc.value) ∧
    framePeak ((runWithTrace store input hC hAd K outer scalar pc hp).2.take steps) ≤
      envelope s K store.width store.cap.value (store.cap.value-pc.value) :=
  BinaryPRGHeapTraceUsage.all_prefix _ _
    (runWithTrace_usage store input source hC hR hCase hAd s hs hH K outer scalar pc hp) borrowed steps

end Blotto.BinaryFourSmallLifetime
