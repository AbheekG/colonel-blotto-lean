import Blotto.BinaryReflectedPreparationLifetime
import Blotto.BinaryPRGHeapNativeLifetimePolynomial
import Blotto.BinaryPRGHeapReflectedSetup

/-! The reflected caller consumes the traced retained setup and the complete
physical source at its incoming absolute cursor. The cache stays in the result
for later terminal work; exact comparison with the former caller is proof-only. -/
namespace Blotto.BinaryPRGHeapReflectedLifetime
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryReflectedFourSetup BinaryReflectedPreparationLifetime BinaryPRGHeapTraceUsage
open BinaryPRGWordControllerBooleanResourceThreeBridge
set_option maxHeartbeats 2000000

def drawPrepared (seed : BinarySeedLookupTree.Store) {input : BinaryFourParameters.Input} (prepared : Prepared input)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    BinaryPRGWordControllerThreeResource.Result seed prepared.capacity × Trace :=
  let drawn := BinaryPRGHeapNativeLifetime.nativeWithTrace seed prepared.capacity prepared.system.initial
    prepared.capacity_canonical prepared.canonical.2.2.2 pc hp
  ((drawn.1.1.map generalCertified_toThree,drawn.1.2),wrap 16 2 [drawn.2])

def transport (seed : BinarySeedLookupTree.Store) {input : BinaryFourParameters.Input} (prepared : Prepared input)
    (result : BinaryPRGWordControllerThreeResource.Result seed prepared.capacity) :
    BinaryPRGWordControllerThreeResource.Result seed (prepare input).capacity :=
  prepared.capacity_source ▸ result

theorem drawPrepared_erasure (seed : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (hC : input.Canonical) (prepared : Prepared input)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    transport seed prepared (drawPrepared seed prepared pc hp).1 =
      BinaryPRGWordControllerThreeResource.setupIndexed seed input hC pc hp := by
  cases prepared with
  | mk parameters hParameters hPC system hSystem hSC capacity hCapacity hCC =>
      cases hSystem
      cases hCapacity
      unfold transport drawPrepared
      dsimp only
      simp only [BinaryPRGHeapNativeLifetime.nativeWithTrace_erasure]
      exact BinaryPRGHeapResourceThreeSource.sourceRun_erasure seed _ _ _ _ pc hp

def runWithTrace (seed : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (Prepared input × BinaryPRGWordControllerThreeResource.Result seed (prepare input).capacity) × Trace :=
  let prepared := BinaryReflectedPreparationLifetime.prepareWithTrace input hC
  let drawn := drawPrepared seed prepared.1 pc hp
  ((prepared.1,transport seed prepared.1 drawn.1),wrap 32 2 [prepared.2,drawn.2])

theorem runWithTrace_erasure (seed : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (runWithTrace seed input hC pc hp).1.2 =
      (BinaryPRGHeapReflectedSetup.run seed input hC pc hp).1 := by
  exact (drawPrepared_erasure seed input hC _ pc hp).trans
    (BinaryPRGHeapReflectedSetup.run_erasure seed input hC pc hp).symm

def envelope (s indexWidth seedCap : ℕ) : ℕ :=
  BinaryReflectedPreparationLifetime.envelope s +
    BinaryPRGHeapThreeNativeLifetimeBound.envelope (expressionHeightBudget s 15) indexWidth seedCap + 64

theorem drawPrepared_usage (seed : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (source : RationalFourInput) (hC : input.Canonical) (hR : input.Refines source)
    (hCase : source.w < (1 - source.p) * source.ell) (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s)
    (prepared : Prepared input) (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    usage (drawPrepared seed prepared pc hp).2 ≤
      BinaryPRGHeapThreeNativeLifetimeBound.envelope (expressionHeightBudget s 15) seed.width seed.cap.value + 20 := by
  have hCap : ∀ j,RationalHeight (value (prepared.capacity.read j)) (expressionHeightBudget s 15) := by
    rw [prepared.capacity_source]
    exact BinaryReflectedResourceWork.capacity_height input source hC hR hCase s hs hH
  have hInitial : ∀ j,RationalHeight (value (prepared.system.initial.read j)) (expressionHeightBudget s 15) := by
    rw [prepared.system_correct]
    exact BinaryReflectedResourceWork.initial_resource_height input source hC hR hCase s hs hH
  have hNative := BinaryPRGHeapThreeNativeLifetimeBound.nativeWithTrace_input_usage (expressionHeightBudget s 15)
    (hs.trans (expressionHeightBudget_ge_input s 15)) seed prepared.capacity prepared.system.initial
    prepared.capacity_canonical prepared.canonical.2.2.2 hCap hInitial pc hp
  have hw := wrap_usage 16 2 [(BinaryPRGHeapNativeLifetime.nativeWithTrace seed prepared.capacity prepared.system.initial
    prepared.capacity_canonical prepared.canonical.2.2.2 pc hp).2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change usage (drawPrepared seed prepared pc hp).2 ≤ _ at hw
  omega

theorem runWithTrace_usage (seed : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (source : RationalFourInput) (hC : input.Canonical) (hR : input.Refines source)
    (hCase : source.w < (1 - source.p) * source.ell) (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    usage (runWithTrace seed input hC pc hp).2 ≤ envelope s seed.width seed.cap.value := by
  let prepared := BinaryReflectedPreparationLifetime.prepareWithTrace input hC
  have hP := BinaryReflectedPreparationLifetime.prepareWithTrace_usage input source hC hR hCase s hs hH
  have hD := drawPrepared_usage seed input source hC hR hCase s hs hH prepared.1 pc hp
  have hw := wrap_usage 32 2 [prepared.2,(drawPrepared seed prepared.1 pc hp).2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change usage (runWithTrace seed input hC pc hp).2 ≤ _ at hw
  change usage prepared.2 ≤ _ at hP
  unfold envelope
  omega

theorem all_prefix (seed : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (source : RationalFourInput) (hC : input.Canonical) (hR : input.Refines source)
    (hCase : source.w < (1 - source.p) * source.ell) (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) (borrowed steps : ℕ) :
    retainedHeap borrowed (runWithTrace seed input hC pc hp).2 steps ≤ borrowed + envelope s seed.width seed.cap.value ∧
      framePeak ((runWithTrace seed input hC pc hp).2.take steps) ≤ envelope s seed.width seed.cap.value :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (runWithTrace_usage seed input source hC hR hCase s hs hH pc hp) borrowed steps

end Blotto.BinaryPRGHeapReflectedLifetime
