import Blotto.BinaryScalarTape
import Blotto.BinarySmallUniformFactoryLifetime
import Blotto.BinaryWordSegmentLifetimeBound
import Blotto.BinaryPRGWordControllerFour
import Blotto.RationalMergeFourHeight

/-! The actually built nine-slot small-uniform descriptor feeds the Boolean-PC
categorical/point draw. Proof-only admissibility fields do not rerun a factory. -/
namespace Blotto.BinaryFourSmallUniformDrawLifetime
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGHeapTraceUsage
set_option maxHeartbeats 2000000

def preparedWithTrace (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinarySmallRootSample.Admissible input) :
    BinaryStoredSegmentProgram.Prepared 4 9 × Trace :=
  let descriptor := BinarySmallUniformFactoryLifetime.fromOriginalWithTrace input
  (⟨descriptor.1,
    by rw [BinarySmallUniformFactoryLifetime.fromOriginalWithTrace_erasure input hC]; exact BinarySmallUniformCompiler.fromOriginal_canonical input hC,
    by rw [BinarySmallUniformFactoryLifetime.fromOriginalWithTrace_erasure input hC]; exact BinarySmallRootSample.uniform_nonnegative input hC hAd⟩,
    descriptor.2)

private theorem prepared_eq {p q : BinaryStoredSegmentProgram.Prepared 4 9}
    (h : p.table = q.table) : p = q := by
  cases p with
  | mk pt pc pn =>
    cases q with
    | mk qt qc qn =>
      dsimp only at h
      cases h
      rfl

theorem preparedWithTrace_erasure (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinarySmallRootSample.Admissible input) :
    (preparedWithTrace input hC hAd).1 = BinaryPRGWordControllerFour.uniformPrepared input hC hAd := by
  apply prepared_eq
  simp only [preparedWithTrace,BinaryPRGWordControllerFour.uniformPrepared]
  exact BinarySmallUniformFactoryLifetime.fromOriginalWithTrace_erasure input hC

def runWithTrace (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (hC : input.Canonical) (hAd : BinarySmallRootSample.Admissible input)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width)
    (hp : pc.value ≤ store.cap.value) : BinaryPRGWordControllerSegment.Result store 4 × Trace :=
  let prepared := preparedWithTrace input hC hAd
  let drawn := BinaryWordSegmentLifetime.runWithTrace store prepared.1 0 K scalar pc hp
  (drawn.1,wrap 32 2 [prepared.2,drawn.2])

theorem runWithTrace_erasure (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (hC : input.Canonical) (hAd : BinarySmallRootSample.Admissible input)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width)
    (hp : pc.value ≤ store.cap.value) :
    (runWithTrace store input hC hAd K scalar pc hp).1 =
      BinaryPRGWordControllerSegment.run store
        (BinaryPRGWordControllerFour.uniformPrepared input hC hAd) 0 K scalar pc hp := by
  unfold runWithTrace
  dsimp only
  rw [BinaryWordSegmentLifetime.runWithTrace_erasure,preparedWithTrace_erasure]

theorem runWithTrace_position (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (hC : input.Canonical) (hAd : BinarySmallRootSample.Admissible input)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width)
    (hp : pc.value ≤ store.cap.value) :
    pc.value ≤ (runWithTrace store input hC hAd K scalar pc hp).1.2.value ∧
      (runWithTrace store input hC hAd K scalar pc hp).1.2.value ≤ store.cap.value :=
  BinaryWordSegmentLifetime.runWithTrace_position store (preparedWithTrace input hC hAd).1 0 K scalar pc hp

def envelope (s K indexWidth seedCap : ℕ) : ℕ :=
  BinarySmallUniformFactoryLifetime.envelope s +
    BinaryWordSegmentLifetimeBound.envelope 4 9 (expressionHeightBudget s 35) K indexWidth seedCap + 64

theorem runWithTrace_usage (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (source : RationalFourInput) (hC : input.Canonical) (hR : input.Refines source)
    (hCase : source.w < (1-source.p)*source.ell) (hAd : BinarySmallRootSample.Admissible input)
    (s : ℕ) (hs : 3 ≤ s) (hH : source.FieldsHeight s)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width)
    (hp : pc.value ≤ store.cap.value) :
    usage (runWithTrace store input hC hAd K scalar pc hp).2 ≤
      envelope s K store.width store.cap.value := by
  let prepared := preparedWithTrace input hC hAd
  let drawn := BinaryWordSegmentLifetime.runWithTrace store prepared.1 0 K scalar pc hp
  have hErasure := preparedWithTrace_erasure input hC hAd
  have hRef : prepared.1.table.Refines (source.smallUniformLottery hCase) := by
    dsimp only [prepared]
    rw [hErasure]
    exact BinarySmallUniformCompiler.fromOriginal_refines input source hC hR hCase
  have hHeight := hH.smallUniformLottery (by omega : 2 ≤ s) hCase
  have hs35 : 3 ≤ expressionHeightBudget s 35 := hs.trans (expressionHeightBudget_ge_input s 35)
  have hFactory := BinarySmallUniformFactoryLifetime.fromOriginalWithTrace_usage input source hC hR hCase s hs hH
  have hDraw := BinaryWordSegmentLifetimeBound.runWithTrace_usage store prepared.1
    (source.smallUniformLottery hCase) hRef (expressionHeightBudget s 35) hs35 hHeight.1 hHeight.2
    0 K scalar pc hp
  change usage prepared.2 ≤ _ at hFactory
  change usage drawn.2 ≤ _ at hDraw
  have hw := wrap_usage 32 2 [prepared.2,drawn.2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change usage (wrap 32 2 [prepared.2,drawn.2]) ≤ _
  unfold envelope
  omega

theorem all_prefix (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (source : RationalFourInput) (hC : input.Canonical) (hR : input.Refines source)
    (hCase : source.w < (1-source.p)*source.ell) (hAd : BinarySmallRootSample.Admissible input)
    (s : ℕ) (hs : 3 ≤ s) (hH : source.FieldsHeight s)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width)
    (hp : pc.value ≤ store.cap.value) (borrowed steps : ℕ) :
    retainedHeap borrowed (runWithTrace store input hC hAd K scalar pc hp).2 steps ≤
      borrowed + envelope s K store.width store.cap.value ∧
    framePeak ((runWithTrace store input hC hAd K scalar pc hp).2.take steps) ≤
      envelope s K store.width store.cap.value :=
  BinaryPRGHeapTraceUsage.all_prefix _ _
    (runWithTrace_usage store input source hC hR hCase hAd s hs hH K scalar pc hp) borrowed steps

end Blotto.BinaryFourSmallUniformDrawLifetime
