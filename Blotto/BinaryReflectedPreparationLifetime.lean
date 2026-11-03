import Blotto.BinaryReflectedSystemLifetime
import Blotto.BinaryReflectedResourceWork

/-! Retain the actual traced parameter table, reflected system and capacity
once. Logical/source equalities and canonical certificates are proof-only. -/
namespace Blotto.BinaryReflectedPreparationLifetime
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryReflectedFourSetup BinaryPRGHeapTraceUsage
set_option maxHeartbeats 2000000

structure Prepared (input : BinaryFourParameters.Input) where
  parameters : FixedArrayTable 8 SignedWord
  parameters_correct : parameters = BinaryFourParameters.prepare input
  parameters_canonical : ∀ j,CanonicalWord (parameters.read j)
  system : System
  system_correct : system = prepare input
  canonical : system.Canonical
  capacity : FixedArrayTable 3 SignedWord
  capacity_correct : capacity = system.capacity
  capacity_canonical : ∀ j,CanonicalWord (capacity.read j)

theorem Prepared.capacity_source {input : BinaryFourParameters.Input} (prepared : Prepared input) :
    prepared.capacity = (prepare input).capacity := by
  rw [prepared.capacity_correct,prepared.system_correct]

def prepareWithTrace (input : BinaryFourParameters.Input) (hC : input.Canonical) : Prepared input × Trace :=
  let parameters := BinaryReflectedParameterLifetime.prepareWithTrace input
  have hParameters := BinaryReflectedParameterLifetime.prepareWithTrace_erasure input hC
  have hPC : ∀ j,CanonicalWord (parameters.1.read j) := by
    rw [hParameters]
    exact BinaryFourParameters.prepare_canonical input hC
  let system := BinaryReflectedSystemLifetime.fromParametersWithTrace input parameters.1
  have hSystem : system.1 = prepare input := by
    rw [BinaryReflectedSystemLifetime.fromParametersWithTrace_erasure input parameters.1 hC hPC,hParameters]
    rfl
  have hSC : system.1.Canonical := by rw [hSystem]; exact prepare_canonical input hC
  let capacity := BinaryReflectedSystemLifetime.capacityWithTrace system.1
  have hCapacity := BinaryReflectedSystemLifetime.capacityWithTrace_erasure system.1 hSC
  (⟨parameters.1,hParameters,hPC,system.1,hSystem,hSC,capacity.1,hCapacity,
      (by rw [hCapacity]; exact capacity_canonical system.1 hSC)⟩,
    wrap 48 4 [parameters.2,system.2,capacity.2])

theorem prepareWithTrace_fields (input : BinaryFourParameters.Input) (hC : input.Canonical) :
    (prepareWithTrace input hC).1.parameters = BinaryFourParameters.prepare input ∧
      (prepareWithTrace input hC).1.system = prepare input ∧
      (prepareWithTrace input hC).1.capacity = (prepare input).capacity :=
  ⟨(prepareWithTrace input hC).1.parameters_correct,(prepareWithTrace input hC).1.system_correct,
    (prepareWithTrace input hC).1.capacity_source⟩

def envelope (s : ℕ) : ℕ :=
  BinaryReflectedParameterLifetime.envelope s +
    BinaryReflectedSystemLifetime.envelope (expressionHeightBudget s 12) +
    BinaryReflectedSystemLifetime.capacityEnvelope (expressionHeightBudget s 14) + 64

theorem prepareWithTrace_usage (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1 - source.p) * source.ell)
    (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s) :
    usage (prepareWithTrace input hC).2 ≤ envelope s := by
  let parameters := BinaryReflectedParameterLifetime.prepareWithTrace input
  have hPE : parameters.1 = BinaryFourParameters.prepare input :=
    BinaryReflectedParameterLifetime.prepareWithTrace_erasure input hC
  have hPC : ∀ j,CanonicalWord (parameters.1.read j) := by
    rw [hPE]
    exact BinaryFourParameters.prepare_canonical input hC
  let system := BinaryReflectedSystemLifetime.fromParametersWithTrace input parameters.1
  have hSE : system.1 = prepare input := by
    rw [BinaryReflectedSystemLifetime.fromParametersWithTrace_erasure input parameters.1 hC hPC,hPE]
    rfl
  have hSC : system.1.Canonical := by rw [hSE]; exact prepare_canonical input hC
  have hParameters : ∀ j,RationalHeight (value (parameters.1.read j)) (expressionHeightBudget s 12) := by
    intro j
    rw [hPE,BinaryFourParameters.prepare_value input source hC hR j]
    exact hH.scalar hs j
  have hLengths : ∀ j,RationalHeight (value ((originalLengths input).read j)) (expressionHeightBudget s 12) := by
    intro j
    rw [originalLengths_value input source hR j]
    exact (hH.originalLengths j).mono (expressionHeightBudget_ge_input s 12)
  have hP := BinaryReflectedParameterLifetime.prepareWithTrace_usage input source hC hR s hs hH
  have hS := BinaryReflectedSystemLifetime.fromParametersWithTrace_usage input parameters.1 hC hPC _ hParameters hLengths
  have hRef := prepare_refines input source hC hR hCase
  have hSourceHeight := hH.reflectedResourceSystem hs hCase
  have hLong : ∀ j,RationalHeight (value (system.1.long.read j)) (expressionHeightBudget s 14) := by
    intro j
    rw [hSE,hRef.2.1 j]
    exact hSourceHeight.2.1 j
  have hShort : ∀ j,RationalHeight (value (system.1.short.read j)) (expressionHeightBudget s 14) := by
    intro j
    rw [hSE,hRef.2.2.1 j]
    exact hSourceHeight.2.2.1 j
  have hCap := BinaryReflectedSystemLifetime.capacityWithTrace_usage system.1 hSC _ hLong hShort
  have hw := wrap_usage 48 4 [parameters.2,system.2,(BinaryReflectedSystemLifetime.capacityWithTrace system.1).2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change usage (wrap 48 4 [parameters.2,system.2,(BinaryReflectedSystemLifetime.capacityWithTrace system.1).2]) ≤ _
  change usage parameters.2 ≤ _ at hP
  change usage system.2 ≤ _ at hS
  unfold envelope
  omega

theorem all_prefix (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1 - source.p) * source.ell)
    (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s) (borrowed steps : ℕ) :
    retainedHeap borrowed (prepareWithTrace input hC).2 steps ≤ borrowed + envelope s ∧
      framePeak ((prepareWithTrace input hC).2.take steps) ≤ envelope s :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (prepareWithTrace_usage input source hC hR hCase s hs hH) borrowed steps

end Blotto.BinaryReflectedPreparationLifetime
