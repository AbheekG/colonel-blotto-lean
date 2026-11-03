import Blotto.BinaryScalarTape
import Blotto.BinaryFourSmallLifetime
import Blotto.BinaryReflectedLowerSampleLifetime

/-! Actual small-root optional execution uses the complete physical lower
fallback only on exhaustion. The returned absolute cursor is unchanged by
fallback, and every input word path yields the old bounded-sampler row. -/
namespace Blotto.BinaryFourSmallFixedLifetime
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGHeapTraceUsage
set_option maxHeartbeats 2000000

def runWithTrace (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (hC : input.Canonical) (hAd : BinarySmallRootSample.Admissible input)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width)
    (hp : pc.value ≤ store.cap.value) : (FixedArrayTable 4 SignedWord × FixedBinaryWord store.width) × Trace :=
  let drawn := BinaryFourSmallLifetime.runWithTrace store input hC hAd K outer scalar pc hp
  match drawn.1.1 with
  | some row => ((row,drawn.1.2),wrap 24 2 [drawn.2])
  | none =>
      let fallback := BinaryReflectedLowerSampleLifetime.sampleWithTrace input hC hAd K outer scalar
      ((fallback.1,drawn.1.2),wrap 32 2 [drawn.2,fallback.2])

theorem runWithTrace_erasure (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (hC : input.Canonical) (hAd : BinarySmallRootSample.Admissible input)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width)
    (hp : pc.value ≤ store.cap.value) :
    (runWithTrace store input hC hAd K outer scalar pc hp).1 =
      let drawn := BinaryPRGWordControllerFour.smallRun store input hC hAd K outer scalar pc hp
      (match drawn.1 with
        | some row => row
        | none => BinaryTerminalFallback.sample input hC hAd K outer scalar,drawn.2) := by
  unfold runWithTrace
  dsimp only
  rw [← BinaryFourSmallLifetime.runWithTrace_erasure store input hC hAd K outer scalar pc hp]
  cases h : (BinaryFourSmallLifetime.runWithTrace store input hC hAd K outer scalar pc hp).1.1 with
  | some row => rfl
  | none =>
      exact Prod.ext (BinaryReflectedLowerSampleLifetime.sampleWithTrace_erasure input hC hAd K outer scalar) rfl

theorem runWithTrace_window (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (hC : input.Canonical) (hAd : BinarySmallRootSample.Admissible input)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width)
    (hp : pc.value ≤ store.cap.value) :
    (runWithTrace store input hC hAd K outer scalar pc hp).1.1 =
      BinarySmallRootSample.fixedSample input hC hAd K (store.cap.value-pc.value) outer scalar
        (WordStateMachine.inputWindow (BinaryWordIndexCoinController.reader store) pc.value
          (store.cap.value-pc.value) (by omega)) := by
  have h := congrArg Prod.fst (BinaryPRGWordControllerFour.smallRun_state store input hC hAd K outer scalar pc hp)
  change (BinaryPRGWordControllerFour.smallRun store input hC hAd K outer scalar pc hp).1 =
    (BinarySmallRootSample.run input hC hAd K (store.cap.value-pc.value) outer scalar
      (WordStateMachine.inputWindow (BinaryWordIndexCoinController.reader store) pc.value
        (store.cap.value-pc.value) (by omega))).1 at h
  rw [runWithTrace_erasure]
  dsimp only
  unfold BinarySmallRootSample.fixedSample
  rw [h]
  rfl

theorem runWithTrace_position (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (hC : input.Canonical) (hAd : BinarySmallRootSample.Admissible input)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width)
    (hp : pc.value ≤ store.cap.value) :
    pc.value ≤ (runWithTrace store input hC hAd K outer scalar pc hp).1.2.value ∧
      (runWithTrace store input hC hAd K outer scalar pc hp).1.2.value ≤ store.cap.value := by
  rw [runWithTrace_erasure]
  exact BinaryPRGWordControllerFour.smallRun_position store input hC hAd K outer scalar pc hp

def envelope (s K i b remaining : ℕ) : ℕ :=
  BinaryFourSmallLifetime.envelope s K i b remaining+BinaryReflectedLowerSampleLifetime.envelope s K+128

theorem runWithTrace_usage (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (source : RationalFourInput) (hC : input.Canonical) (hR : input.Refines source)
    (hCase : source.w < (1-source.p)*source.ell) (hAd : BinarySmallRootSample.Admissible input)
    (s : ℕ) (hs : 3 ≤ s) (hH : source.FieldsHeight s)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width)
    (hp : pc.value ≤ store.cap.value) :
    usage (runWithTrace store input hC hAd K outer scalar pc hp).2 ≤
      envelope s K store.width store.cap.value (store.cap.value-pc.value) := by
  let drawn := BinaryFourSmallLifetime.runWithTrace store input hC hAd K outer scalar pc hp
  have hD := BinaryFourSmallLifetime.runWithTrace_usage store input source hC hR hCase hAd s hs hH K outer scalar pc hp
  have hF := BinaryReflectedLowerSampleLifetime.sampleWithTrace_usage input source hC hR hCase hAd s (by omega) hH K outer scalar
  change usage drawn.2 ≤ _ at hD
  unfold runWithTrace
  dsimp only
  split
  · have hw := wrap_usage 24 2 [drawn.2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change usage (wrap 24 2 [drawn.2]) ≤ _
    unfold envelope
    omega
  · have hw := wrap_usage 32 2 [drawn.2,
      (BinaryReflectedLowerSampleLifetime.sampleWithTrace input hC hAd K outer scalar).2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change usage (wrap 32 2 [drawn.2,
      (BinaryReflectedLowerSampleLifetime.sampleWithTrace input hC hAd K outer scalar).2]) ≤ _
    unfold envelope
    omega

theorem all_prefix (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (source : RationalFourInput) (hC : input.Canonical) (hR : input.Refines source)
    (hCase : source.w < (1-source.p)*source.ell) (hAd : BinarySmallRootSample.Admissible input)
    (s : ℕ) (hs : 3 ≤ s) (hH : source.FieldsHeight s)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width)
    (hp : pc.value ≤ store.cap.value) (borrowed steps : ℕ) :
    retainedHeap borrowed (runWithTrace store input hC hAd K outer scalar pc hp).2 steps ≤
      borrowed+envelope s K store.width store.cap.value (store.cap.value-pc.value) ∧
    framePeak ((runWithTrace store input hC hAd K outer scalar pc hp).2.take steps) ≤
      envelope s K store.width store.cap.value (store.cap.value-pc.value) :=
  BinaryPRGHeapTraceUsage.all_prefix _ _
    (runWithTrace_usage store input source hC hR hCase hAd s hs hH K outer scalar pc hp) borrowed steps

theorem runWithTrace_canonical (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (hC : input.Canonical) (hAd : BinarySmallRootSample.Admissible input)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    ∀ j,CanonicalWord ((runWithTrace store input hC hAd K outer scalar pc hp).1.1.read j) := by
  rw [runWithTrace_window]
  exact BinarySmallRootSample.fixedSample_canonical input hC hAd K _ outer scalar _

theorem runWithTrace_fullBudget (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (source : RationalFourInput) (hC : input.Canonical) (hR : input.Refines source)
    (hCase : source.w < (1-source.p)*source.ell) (hAd : BinarySmallRootSample.Admissible input)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    FullBudget (source.B : ℝ)
      (fun j => (value ((runWithTrace store input hC hAd K outer scalar pc hp).1.1.read j) : ℝ)) := by
  rw [runWithTrace_window]
  exact BinarySmallRootSample.fixedSample_fullBudget input source hC hR hCase hAd K _ outer scalar _

theorem runWithTrace_inBox (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (source : RationalFourInput) (hC : input.Canonical) (hR : input.Refines source)
    (hCase : source.w < (1-source.p)*source.ell) (hAd : BinarySmallRootSample.Admissible input)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    InBox ![(source.u : ℝ),(source.v : ℝ),(source.w : ℝ),(source.ell : ℝ)]
      (fun j => (value ((runWithTrace store input hC hAd K outer scalar pc hp).1.1.read j) : ℝ)) := by
  rw [runWithTrace_window]
  exact BinarySmallRootSample.fixedSample_inBox input source hC hR hCase hAd K _ outer scalar _

end Blotto.BinaryFourSmallFixedLifetime
