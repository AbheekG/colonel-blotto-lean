import Blotto.BinaryPRGHeapLowerSourceBound
import Blotto.BinaryLowerThreeBridge
import Blotto.BinaryReflectedPreparationLifetime

/-! Deterministic reflected lower completion consumes actual retained setup
arrays, executes complete physical source/loop/native materialization and
retains the same cache for subsequent terminal/profile work. -/
namespace Blotto.BinaryReflectedLowerLifetime
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGHeapTraceUsage BinaryReflectedPreparationLifetime BinaryReflectedFourSetup
open BinaryPRGWordControllerBooleanResourceThreeBridge
set_option maxHeartbeats 2000000

def fromPreparedWithTrace {input : BinaryFourParameters.Input} (prepared : Prepared input) :
    BinaryThreeResourcePair.Certified (prepare input).capacity × Trace :=
  let lower := BinaryPRGHeapLowerSourceLifetime.nativeWithTrace prepared.capacity prepared.system.initial
    prepared.capacity_canonical prepared.canonical.2.2.2
  let state := generalCertified_toThree lower.1
  let transported : BinaryThreeResourcePair.Certified (prepare input).capacity := prepared.capacity_source ▸ state
  (transported,wrap 16 2 [lower.2])

theorem fromPreparedWithTrace_erasure (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (prepared : Prepared input) :
    (fromPreparedWithTrace prepared).1 = BinaryResourceFallback.setup input hC := by
  cases prepared with
  | mk parameters hParameters hPC system hSystem hSC capacity hCapacity hCC =>
      cases hSystem
      cases hCapacity
      unfold fromPreparedWithTrace
      dsimp only
      rw [BinaryPRGHeapLowerSourceLifetime.nativeWithTrace_erasure,BinaryLowerThreeBridge.lower_toThree]
      rfl

def runWithTrace (input : BinaryFourParameters.Input) (hC : input.Canonical) :
    (Prepared input × BinaryThreeResourcePair.Certified (prepare input).capacity) × Trace :=
  let prepared := BinaryReflectedPreparationLifetime.prepareWithTrace input hC
  let lower := fromPreparedWithTrace prepared.1
  ((prepared.1,lower.1),wrap 32 2 [prepared.2,lower.2])

theorem runWithTrace_erasure (input : BinaryFourParameters.Input) (hC : input.Canonical) :
    (runWithTrace input hC).1.2 = BinaryResourceFallback.setup input hC :=
  fromPreparedWithTrace_erasure input hC _

def envelope (s : ℕ) : ℕ :=
  BinaryReflectedPreparationLifetime.envelope s +
    BinaryPRGHeapLowerSourceBound.envelope (expressionHeightBudget s 15)+64

theorem fromPreparedWithTrace_usage (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1-source.p)*source.ell)
    (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s) (prepared : Prepared input) :
    usage (fromPreparedWithTrace prepared).2 ≤ BinaryPRGHeapLowerSourceBound.envelope (expressionHeightBudget s 15)+20 := by
  have hCap : ∀ j,RationalHeight (value (prepared.capacity.read j)) (expressionHeightBudget s 15) := by
    rw [prepared.capacity_source]
    exact BinaryReflectedResourceWork.capacity_height input source hC hR hCase s hs hH
  have hInitial : ∀ j,RationalHeight (value (prepared.system.initial.read j)) (expressionHeightBudget s 15) := by
    rw [prepared.system_correct]
    exact BinaryReflectedResourceWork.initial_resource_height input source hC hR hCase s hs hH
  have h := BinaryPRGHeapLowerSourceBound.nativeWithTrace_usage _ (hs.trans (expressionHeightBudget_ge_input s 15))
    prepared.capacity prepared.system.initial prepared.capacity_canonical prepared.canonical.2.2.2 hCap hInitial
  have hw := wrap_usage 16 2 [(BinaryPRGHeapLowerSourceLifetime.nativeWithTrace prepared.capacity prepared.system.initial
    prepared.capacity_canonical prepared.canonical.2.2.2).2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change usage (fromPreparedWithTrace prepared).2 ≤ _ at hw
  omega

theorem runWithTrace_usage (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1-source.p)*source.ell)
    (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s) :
    usage (runWithTrace input hC).2 ≤ envelope s := by
  let prepared := BinaryReflectedPreparationLifetime.prepareWithTrace input hC
  have hP := BinaryReflectedPreparationLifetime.prepareWithTrace_usage input source hC hR hCase s hs hH
  have hL := fromPreparedWithTrace_usage input source hC hR hCase s hs hH prepared.1
  have hw := wrap_usage 32 2 [prepared.2,(fromPreparedWithTrace prepared.1).2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change usage (runWithTrace input hC).2 ≤ _ at hw
  change usage prepared.2 ≤ _ at hP
  unfold envelope
  omega

theorem all_prefix (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1-source.p)*source.ell)
    (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s) (borrowed steps : ℕ) :
    retainedHeap borrowed (runWithTrace input hC).2 steps ≤ borrowed+envelope s ∧
      framePeak ((runWithTrace input hC).2.take steps) ≤ envelope s :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (runWithTrace_usage input source hC hR hCase s hs hH) borrowed steps

end Blotto.BinaryReflectedLowerLifetime
