import Blotto.BinaryLifetimeArrayExtras
import Blotto.BinaryFourParametersMeasured
import Blotto.BinaryThreeFactoryMeasured
import Blotto.BinaryFourGluingParentsLifetime

/-! The actual measured eight-word parameter table is shared by both measured
three-variable parents. Original six-field heights and the reached gluing case
derive work and retained-source bounds. Native model prices remain separate. -/

namespace Blotto.BinaryFourGluingParentsMeasured
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryFourParentCompiler
set_option autoImplicit false
set_option maxHeartbeats 3500000

set_option cleanup.letToHave false in
def runWithExtras (input : BinaryFourParameters.Input) (hC : input.Canonical) : (((FixedArrayTable 8 SignedWord × BinaryStoredOverlapEnvironment.Segment 3 9 ×
      BinaryStoredOverlapEnvironment.Segment 3 9) × Trace) × ℕ) × ℕ :=
  let parameters := BinaryFourParametersMeasured.prepareWithExtras input
  let first := BinaryThreeFactoryMeasured.descriptorWithExtras (firstInput input parameters.1.1.1)
  let second := BinaryThreeFactoryMeasured.descriptorWithExtras (secondInput input parameters.1.1.1)
  ((((parameters.1.1.1,first.1.1.1,second.1.1.1),wrap 64 4 [parameters.1.1.2,first.1.1.2,second.1.1.2]),
    parameters.1.2+first.1.2+second.1.2+8),parameters.2+first.2+second.2)

def run (input : BinaryFourParameters.Input) (hC : input.Canonical) :
    ((FixedArrayTable 8 SignedWord × BinaryStoredOverlapEnvironment.Segment 3 9 ×
      BinaryStoredOverlapEnvironment.Segment 3 9) × Trace) × ℕ :=
  (runWithExtras input hC).1

theorem runWithExtras_compat (input : BinaryFourParameters.Input) (hC : input.Canonical) :
    (runWithExtras input hC).1 = run input hC := rfl

theorem run_record (input : BinaryFourParameters.Input) (hC : input.Canonical) :
    run input hC =
  let parameters := BinaryFourParametersMeasured.prepare input
  let first := BinaryThreeFactoryMeasured.descriptor (firstInput input parameters.1.1)
  let second := BinaryThreeFactoryMeasured.descriptor (secondInput input parameters.1.1)
  (((parameters.1.1,first.1.1,second.1.1),wrap 64 4 [parameters.1.2,first.1.2,second.1.2]),
    parameters.2+first.2+second.2+8) := by
  simp only [run,runWithExtras,BinaryLifetimeArrayExtras.build_record,BinaryThreeFactoryMeasured.orderedWithExtras_compat,BinaryThreeFactoryMeasured.descriptorWithExtras_compat,BinaryFourParametersMeasured.prepareWithExtras_compat]

theorem run_data (input : BinaryFourParameters.Input) (hC : input.Canonical) :
    (run input hC).1.1 = (BinaryFourGluingParentsLifetime.runWithTrace input hC).1 := by
  simp only [run_record,BinaryFourGluingParentsLifetime.runWithTrace,BinaryFourParametersMeasured.prepare_data,
    BinaryThreeFactoryMeasured.descriptor_data]

theorem first_canonical (input : BinaryFourParameters.Input) (hC : input.Canonical) :
    (run input hC).1.1.2.1.Canonical := by
  rw [run_data]
  exact BinaryFourGluingParentsLifetime.first_canonical input hC

theorem second_canonical (input : BinaryFourParameters.Input) (hC : input.Canonical) :
    (run input hC).1.1.2.2.Canonical := by
  rw [run_data]
  exact BinaryFourGluingParentsLifetime.second_canonical input hC

theorem interval_canonical (input : BinaryFourParameters.Input) (hC : input.Canonical) :
    CanonicalWord ((run input hC).1.1.1.read 1) := by
  rw [run_data]
  exact BinaryFourGluingParentsLifetime.interval_canonical input hC

def workEnvelope (s : ℕ) : ℕ := BinaryFourParametersMeasured.workEnvelope s+
  2*BinaryThreeFactoryMeasured.workEnvelope (expressionHeightBudget s 12)+8
def envelope (s : ℕ) : ℕ := BinaryFourParametersMeasured.envelope s+
  2*BinaryThreeFactoryMeasured.envelope (expressionHeightBudget s 12)+80

theorem run_bounds (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : (1-source.p)*source.ell ≤ source.w)
    (s : ℕ) (hs : 3 ≤ s) (hH : source.FieldsHeight s) :
    (run input hC).2 ≤ workEnvelope s ∧ usage (run input hC).1.2 ≤ envelope s := by
  let parameters := BinaryFourParametersMeasured.prepare input
  let first := BinaryThreeFactoryMeasured.descriptor (firstInput input parameters.1.1)
  let second := BinaryThreeFactoryMeasured.descriptor (secondInput input parameters.1.1)
  have hP : parameters.1.1 = BinaryFourParameters.prepare input :=
    (BinaryFourParametersMeasured.prepare_data input).trans (BinaryReflectedParameterLifetime.prepareWithTrace_erasure input hC)
  have hCFirst : (firstInput input parameters.1.1).Canonical := by rw [hP]; exact firstInput_canonical input hC
  have hCSecond : (secondInput input parameters.1.1).Canonical := by rw [hP]; exact secondInput_canonical input hC
  have hFirstH : BinaryOrderedThreeFactoryWork.InputHeight (firstInput input parameters.1.1) (expressionHeightBudget s 12) := by
    rw [hP]
    exact BinaryFourGluingParentsLifetime.input_height_of_refines _ _ (firstInput_refines input source hC hR hCase) _
      (hH.gluingFirst_environment (by omega) hCase)
  have hSecondH : BinaryOrderedThreeFactoryWork.InputHeight (secondInput input parameters.1.1) (expressionHeightBudget s 12) := by
    rw [hP]
    exact BinaryFourGluingParentsLifetime.input_height_of_refines _ _ (secondInput_refines input source hC hR hCase) _
      (hH.gluingSecond_environment (by omega) hCase)
  have hs12 : 3 ≤ expressionHeightBudget s 12 := hs.trans (expressionHeightBudget_ge_input s 12)
  have hParameters := BinaryFourParametersMeasured.prepare_bounds input source hC hR s (by omega) hH
  have hFirst := BinaryThreeFactoryMeasured.descriptor_bounds (firstInput input parameters.1.1) hCFirst _ hs12 hFirstH
  have hSecond := BinaryThreeFactoryMeasured.descriptor_bounds (secondInput input parameters.1.1) hCSecond _ hs12 hSecondH
  change parameters.2 ≤ _ ∧ usage parameters.1.2 ≤ _ at hParameters
  change first.2 ≤ _ ∧ usage first.1.2 ≤ _ at hFirst
  change second.2 ≤ _ ∧ usage second.1.2 ≤ _ at hSecond
  have hw := wrap_usage 64 4 [parameters.1.2,first.1.2,second.1.2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  rw [run_record]
  change parameters.2+first.2+second.2+8 ≤ _ ∧ usage (wrap 64 4 [parameters.1.2,first.1.2,second.1.2]) ≤ _
  unfold workEnvelope envelope
  exact ⟨by omega,by omega⟩

theorem all_prefix (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : (1-source.p)*source.ell ≤ source.w)
    (s : ℕ) (hs : 3 ≤ s) (hH : source.FieldsHeight s) (borrowed steps : ℕ) :
    retainedHeap borrowed (run input hC).1.2 steps ≤ borrowed+envelope s ∧
      framePeak ((run input hC).1.2.take steps) ≤ envelope s :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (run_bounds input source hC hR hCase s hs hH).2 borrowed steps

end Blotto.BinaryFourGluingParentsMeasured
