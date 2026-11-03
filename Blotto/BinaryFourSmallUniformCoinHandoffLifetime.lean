import Blotto.BinaryScalarTape
import Blotto.BinaryFourSmallUniformDrawLifetime
import Blotto.BinaryFourSmallCoinLifetime

/-! The actual root coin hands its returned absolute Boolean cursor to the
traced uniform factory/draw. The true-branch premise is proof-only. -/
namespace Blotto.BinaryFourSmallUniformCoinHandoffLifetime
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGHeapTraceUsage
set_option maxHeartbeats 2000000

def afterRootWithTrace (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (hC : input.Canonical) (hAd : BinarySmallRootSample.Admissible input)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width)
    (hp : pc.value ≤ store.cap.value)
    (root : (Option Bool × FixedBinaryWord store.width) × Trace)
    (hRoot : root = BinaryFourSmallCoinLifetime.sampleWithTrace store input pc hp) :
    BinaryPRGWordControllerFour.Result store × Trace :=
  let drawn := BinaryFourSmallUniformDrawLifetime.runWithTrace store input hC hAd K scalar root.1.2
    (by rw [hRoot]; exact (BinaryFourSmallCoinLifetime.sampleWithTrace_position store input pc hp).2)
  (drawn.1,wrap 32 2 [root.2,drawn.2])

def runWithTrace (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (hC : input.Canonical) (hAd : BinarySmallRootSample.Admissible input)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width)
    (hp : pc.value ≤ store.cap.value) : BinaryPRGWordControllerFour.Result store × Trace :=
  let root := BinaryFourSmallCoinLifetime.sampleWithTrace store input pc hp
  afterRootWithTrace store input hC hAd K scalar pc hp root rfl

theorem runWithTrace_old_true_branch (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (hC : input.Canonical) (hAd : BinarySmallRootSample.Admissible input)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width)
    (hp : pc.value ≤ store.cap.value)
    (hTrue : (BinaryFourSmallCoinLifetime.sampleWithTrace store input pc hp).1.1 = some true) :
    (runWithTrace store input hC hAd K scalar pc hp).1 =
      BinaryPRGWordControllerFour.smallRun store input hC hAd K outer scalar pc hp := by
  have hRoot := BinaryFourSmallCoinLifetime.sampleWithTrace_erasure store input pc hp
  have hOldTrue :
      (BinaryPRGWordControllerDataCoin.sample store
        (BinaryPRGWordControllerFour.probability input) pc hp).1 = some true := by
    rw [← hRoot]
    exact hTrue
  have hCursor := congrArg Prod.snd hRoot
  unfold runWithTrace afterRootWithTrace
  dsimp only
  rw [BinaryFourSmallUniformDrawLifetime.runWithTrace_erasure]
  unfold BinaryPRGWordControllerFour.smallRun
  dsimp only
  simp only [hOldTrue]
  simpa only [hCursor]

theorem runWithTrace_position (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (hC : input.Canonical) (hAd : BinarySmallRootSample.Admissible input)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width)
    (hp : pc.value ≤ store.cap.value) :
    pc.value ≤ (runWithTrace store input hC hAd K scalar pc hp).1.2.value ∧
      (runWithTrace store input hC hAd K scalar pc hp).1.2.value ≤ store.cap.value := by
  have hRoot := BinaryFourSmallCoinLifetime.sampleWithTrace_position store input pc hp
  have hDraw := BinaryFourSmallUniformDrawLifetime.runWithTrace_position store input hC hAd K scalar
    (BinaryFourSmallCoinLifetime.sampleWithTrace store input pc hp).1.2 hRoot.2
  change pc.value ≤ _ ∧ _ ≤ _
  exact ⟨hRoot.1.trans hDraw.1,hDraw.2⟩

def envelope (s K indexWidth seedCap remaining : ℕ) : ℕ :=
  BinaryFourSmallCoinLifetime.envelope s indexWidth remaining +
    BinaryFourSmallUniformDrawLifetime.envelope s K indexWidth seedCap + 64

theorem runWithTrace_usage (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (source : RationalFourInput) (hC : input.Canonical) (hR : input.Refines source)
    (hCase : source.w < (1-source.p)*source.ell) (hAd : BinarySmallRootSample.Admissible input)
    (s : ℕ) (hs : 3 ≤ s) (hH : source.FieldsHeight s)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width)
    (hp : pc.value ≤ store.cap.value) :
    usage (runWithTrace store input hC hAd K scalar pc hp).2 ≤
      envelope s K store.width store.cap.value (store.cap.value-pc.value) := by
  let root := BinaryFourSmallCoinLifetime.sampleWithTrace store input pc hp
  let drawn := BinaryFourSmallUniformDrawLifetime.runWithTrace store input hC hAd K scalar root.1.2
    (BinaryFourSmallCoinLifetime.sampleWithTrace_position store input pc hp).2
  have hRoot := BinaryFourSmallCoinLifetime.sampleWithTrace_usage store input source hC hR s hH pc hp
  have hDraw := BinaryFourSmallUniformDrawLifetime.runWithTrace_usage store input source hC hR hCase hAd
    s hs hH K scalar root.1.2 (BinaryFourSmallCoinLifetime.sampleWithTrace_position store input pc hp).2
  change usage root.2 ≤ _ at hRoot
  change usage drawn.2 ≤ _ at hDraw
  have hw := wrap_usage 32 2 [root.2,drawn.2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change usage (wrap 32 2 [root.2,drawn.2]) ≤ _
  unfold envelope
  omega

theorem all_prefix (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (source : RationalFourInput) (hC : input.Canonical) (hR : input.Refines source)
    (hCase : source.w < (1-source.p)*source.ell) (hAd : BinarySmallRootSample.Admissible input)
    (s : ℕ) (hs : 3 ≤ s) (hH : source.FieldsHeight s)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width)
    (hp : pc.value ≤ store.cap.value) (borrowed steps : ℕ) :
    retainedHeap borrowed (runWithTrace store input hC hAd K scalar pc hp).2 steps ≤
      borrowed + envelope s K store.width store.cap.value (store.cap.value-pc.value) ∧
    framePeak ((runWithTrace store input hC hAd K scalar pc hp).2.take steps) ≤
      envelope s K store.width store.cap.value (store.cap.value-pc.value) :=
  BinaryPRGHeapTraceUsage.all_prefix _ _
    (runWithTrace_usage store input source hC hR hCase hAd s hs hH K scalar pc hp) borrowed steps

theorem afterRootWithTrace_old_true_branch (store : BinarySeedLookupTree.Store)
    (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinarySmallRootSample.Admissible input)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width)
    (hp : pc.value ≤ store.cap.value)
    (root : (Option Bool × FixedBinaryWord store.width) × Trace)
    (hRoot : root = BinaryFourSmallCoinLifetime.sampleWithTrace store input pc hp)
    (hTrue : root.1.1 = some true) :
    (afterRootWithTrace store input hC hAd K scalar pc hp root hRoot).1 =
      BinaryPRGWordControllerFour.smallRun store input hC hAd K outer scalar pc hp := by
  subst root
  exact runWithTrace_old_true_branch store input hC hAd K outer scalar pc hp hTrue

theorem afterRootWithTrace_usage (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (source : RationalFourInput) (hC : input.Canonical) (hR : input.Refines source)
    (hCase : source.w < (1-source.p)*source.ell) (hAd : BinarySmallRootSample.Admissible input)
    (s : ℕ) (hs : 3 ≤ s) (hH : source.FieldsHeight s)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width)
    (hp : pc.value ≤ store.cap.value)
    (root : (Option Bool × FixedBinaryWord store.width) × Trace)
    (hRoot : root = BinaryFourSmallCoinLifetime.sampleWithTrace store input pc hp) :
    usage (afterRootWithTrace store input hC hAd K scalar pc hp root hRoot).2 ≤
      envelope s K store.width store.cap.value (store.cap.value-pc.value) := by
  subst root
  exact runWithTrace_usage store input source hC hR hCase hAd s hs hH K scalar pc hp

theorem afterRootWithTrace_position (store : BinarySeedLookupTree.Store)
    (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinarySmallRootSample.Admissible input)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width)
    (hp : pc.value ≤ store.cap.value)
    (root : (Option Bool × FixedBinaryWord store.width) × Trace)
    (hRoot : root = BinaryFourSmallCoinLifetime.sampleWithTrace store input pc hp) :
    pc.value ≤ (afterRootWithTrace store input hC hAd K scalar pc hp root hRoot).1.2.value ∧
      (afterRootWithTrace store input hC hAd K scalar pc hp root hRoot).1.2.value ≤ store.cap.value := by
  subst root
  exact runWithTrace_position store input hC hAd K scalar pc hp

theorem afterRootWithTrace_all_prefix (store : BinarySeedLookupTree.Store)
    (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source)
    (hCase : source.w < (1-source.p)*source.ell)
    (hAd : BinarySmallRootSample.Admissible input)
    (s : ℕ) (hs : 3 ≤ s) (hH : source.FieldsHeight s)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width)
    (hp : pc.value ≤ store.cap.value)
    (root : (Option Bool × FixedBinaryWord store.width) × Trace)
    (hRoot : root = BinaryFourSmallCoinLifetime.sampleWithTrace store input pc hp)
    (borrowed steps : ℕ) :
    retainedHeap borrowed (afterRootWithTrace store input hC hAd K scalar pc hp root hRoot).2 steps ≤
      borrowed + envelope s K store.width store.cap.value (store.cap.value-pc.value) ∧
    framePeak ((afterRootWithTrace store input hC hAd K scalar pc hp root hRoot).2.take steps) ≤
      envelope s K store.width store.cap.value (store.cap.value-pc.value) :=
  BinaryPRGHeapTraceUsage.all_prefix _ _
    (afterRootWithTrace_usage store input source hC hR hCase hAd s hs hH K scalar pc hp root hRoot)
    borrowed steps

end Blotto.BinaryFourSmallUniformCoinHandoffLifetime
