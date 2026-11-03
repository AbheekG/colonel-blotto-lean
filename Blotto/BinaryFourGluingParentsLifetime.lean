import Blotto.BinaryFourGuardLifetime
import Blotto.BinaryReflectedParameterLifetime
import Blotto.BinaryUnorderedThreeLifetime
import Blotto.RationalFourGluingHeight

/-! Original six words produce one actual eight-word parameter table and both
complete unordered three-variable parent descriptors for the gluing branch.
The table is shared by the two parents; every source array and frame is kept. -/
namespace Blotto.BinaryFourGluingParentsLifetime
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGHeapTraceUsage BinaryFourParentCompiler
set_option maxHeartbeats 2000000

def runWithTrace (input : BinaryFourParameters.Input) (hC : input.Canonical) :
    (FixedArrayTable 8 SignedWord × BinaryStoredOverlapEnvironment.Segment 3 9 ×
      BinaryStoredOverlapEnvironment.Segment 3 9) × Trace :=
  let parameters := BinaryReflectedParameterLifetime.prepareWithTrace input
  let first := BinaryUnorderedThreeLifetime.descriptorWithTrace (firstInput input parameters.1)
  let second := BinaryUnorderedThreeLifetime.descriptorWithTrace (secondInput input parameters.1)
  ((parameters.1,first.1,second.1),wrap 64 4 [parameters.2,first.2,second.2])

theorem runWithTrace_erasure (input : BinaryFourParameters.Input) (hC : input.Canonical) :
    (runWithTrace input hC).1 =
      (BinaryFourParameters.prepare input,firstParent input (BinaryFourParameters.prepare input),
        secondParent input (BinaryFourParameters.prepare input)) := by
  unfold runWithTrace firstParent secondParent
  dsimp only
  rw [BinaryReflectedParameterLifetime.prepareWithTrace_erasure input hC]
  rw [BinaryUnorderedThreeLifetime.descriptorWithTrace_erasure _ (firstInput_canonical input hC),
    BinaryUnorderedThreeLifetime.descriptorWithTrace_erasure _ (secondInput_canonical input hC)]

theorem first_canonical (input : BinaryFourParameters.Input) (hC : input.Canonical) :
    (runWithTrace input hC).1.2.1.Canonical := by
  rw [runWithTrace_erasure input hC]
  exact BinaryThreeSpecCompiler.descriptor_canonical _ (firstInput_canonical input hC)

theorem second_canonical (input : BinaryFourParameters.Input) (hC : input.Canonical) :
    (runWithTrace input hC).1.2.2.Canonical := by
  rw [runWithTrace_erasure input hC]
  exact BinaryThreeSpecCompiler.descriptor_canonical _ (secondInput_canonical input hC)

theorem interval_canonical (input : BinaryFourParameters.Input) (hC : input.Canonical) :
    CanonicalWord ((runWithTrace input hC).1.1.read 1) := by
  rw [runWithTrace_erasure input hC]
  exact BinaryFourParameters.prepare_canonical input hC 1

theorem input_height_of_refines (input : BinaryThreeInputCompiler.Input) (source : RationalThreeSpec)
    (hR : BinaryThreeSpecCompiler.Refines input source) (s : ℕ)
    (hEnv : ∀ j,RationalHeight ((RationalThreeSpecCode.environment source).read j) s) :
    BinaryOrderedThreeFactoryWork.InputHeight input s := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · rw [hR.1]; simpa [RationalThreeSpecCode.environment,FixedArrayTable.read_ofFn] using hEnv 0
  · rw [hR.2.1]; simpa [RationalThreeSpecCode.environment,FixedArrayTable.read_ofFn] using hEnv 1
  · rw [hR.2.2.1]; simpa [RationalThreeSpecCode.environment,FixedArrayTable.read_ofFn] using hEnv 2
  · rw [hR.2.2.2.1]; simpa [RationalThreeSpecCode.environment,FixedArrayTable.read_ofFn] using hEnv 3
  · rw [hR.2.2.2.2]; simpa [RationalThreeSpecCode.environment,FixedArrayTable.read_ofFn] using hEnv 4

def envelope (s : ℕ) : ℕ :=
  BinaryReflectedParameterLifetime.envelope s +
    2 * BinaryUnorderedThreeLifetime.envelope (expressionHeightBudget s 12) + 80

theorem runWithTrace_usage (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source)
    (hCase : (1-source.p)*source.ell ≤ source.w) (s : ℕ) (hs : 3 ≤ s) (hH : source.FieldsHeight s) :
    usage (runWithTrace input hC).2 ≤ envelope s := by
  let parameters := BinaryReflectedParameterLifetime.prepareWithTrace input
  let first := BinaryUnorderedThreeLifetime.descriptorWithTrace (firstInput input parameters.1)
  let second := BinaryUnorderedThreeLifetime.descriptorWithTrace (secondInput input parameters.1)
  have hP := BinaryReflectedParameterLifetime.prepareWithTrace_erasure input hC
  have hCFirst : (firstInput input parameters.1).Canonical := by
    rw [hP]
    exact firstInput_canonical input hC
  have hCSecond : (secondInput input parameters.1).Canonical := by
    rw [hP]
    exact secondInput_canonical input hC
  have hHeightFirst : BinaryOrderedThreeFactoryWork.InputHeight (firstInput input parameters.1)
      (expressionHeightBudget s 12) := by
    rw [hP]
    exact input_height_of_refines _ _ (firstInput_refines input source hC hR hCase) _
      (hH.gluingFirst_environment (by omega) hCase)
  have hHeightSecond : BinaryOrderedThreeFactoryWork.InputHeight (secondInput input parameters.1)
      (expressionHeightBudget s 12) := by
    rw [hP]
    exact input_height_of_refines _ _ (secondInput_refines input source hC hR hCase) _
      (hH.gluingSecond_environment (by omega) hCase)
  have hs12 : 3 ≤ expressionHeightBudget s 12 := hs.trans (expressionHeightBudget_ge_input s 12)
  have hParameters := BinaryReflectedParameterLifetime.prepareWithTrace_usage input source hC hR s (by omega) hH
  have hFirst := BinaryUnorderedThreeLifetime.descriptorWithTrace_usage (firstInput input parameters.1)
    hCFirst _ hs12 hHeightFirst
  have hSecond := BinaryUnorderedThreeLifetime.descriptorWithTrace_usage (secondInput input parameters.1)
    hCSecond _ hs12 hHeightSecond
  change usage parameters.2 ≤ _ at hParameters
  change usage first.2 ≤ _ at hFirst
  change usage second.2 ≤ _ at hSecond
  have hw := wrap_usage 64 4 [parameters.2,first.2,second.2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change usage (wrap 64 4 [parameters.2,first.2,second.2]) ≤ _
  unfold envelope
  omega

theorem all_prefix (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source)
    (hCase : (1-source.p)*source.ell ≤ source.w) (s : ℕ) (hs : 3 ≤ s) (hH : source.FieldsHeight s)
    (borrowed steps : ℕ) :
    retainedHeap borrowed (runWithTrace input hC).2 steps ≤ borrowed + envelope s ∧
      framePeak ((runWithTrace input hC).2.take steps) ≤ envelope s :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (runWithTrace_usage input source hC hR hCase s hs hH) borrowed steps

end Blotto.BinaryFourGluingParentsLifetime
