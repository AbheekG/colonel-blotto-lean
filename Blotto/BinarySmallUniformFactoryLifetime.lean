import Blotto.BinarySmallUniformDescriptorLifetime

/-! Original six stored words feed the traced scale preparation, merged
three-variable descriptor and every nine-slot endpoint split exactly once. -/
namespace Blotto.BinarySmallUniformFactoryLifetime
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGHeapTraceUsage
set_option maxHeartbeats 2000000

def fromOriginalWithTrace (input : BinaryFourParameters.Input) :
    BinaryStoredOverlapEnvironment.Segment 4 9 × Trace :=
  let prepared := BinarySmallUniformPreparationLifetime.prepareWithTrace input
  let table := BinarySmallUniformDescriptorLifetime.descriptorWithTrace prepared.1
  (table.1,wrap 64 3 [prepared.2,table.2])

theorem data_projection (input : BinaryFourParameters.Input) :
    (fromOriginalWithTrace input).1 =
      (BinarySmallUniformDescriptorLifetime.descriptorWithTrace
        (BinarySmallUniformPreparationLifetime.prepareWithTrace input).1).1 := by
  simp only [fromOriginalWithTrace]

theorem fromOriginalWithTrace_erasure (input : BinaryFourParameters.Input) (hC : input.Canonical) :
    (fromOriginalWithTrace input).1 = BinarySmallUniformCompiler.fromOriginal input := by
  let prepared := BinarySmallUniformPreparationLifetime.prepareWithTrace input
  have hPrepared := BinarySmallUniformPreparationLifetime.prepareWithTrace_erasure input hC
  have hPC : prepared.1.Canonical := by
    rw [hPrepared]
    exact BinarySmallUniformCompiler.prepare_canonical input hC
  calc
    _ = (BinarySmallUniformDescriptorLifetime.descriptorWithTrace prepared.1).1 := data_projection input
    _ = BinarySmallUniformCompiler.descriptor prepared.1 :=
      BinarySmallUniformDescriptorLifetime.descriptorWithTrace_erasure prepared.1 hPC
    _ = BinarySmallUniformCompiler.fromOriginal input := by
      rw [hPrepared]
      rfl

def envelope (s : ℕ) : ℕ :=
  BinarySmallUniformPreparationLifetime.envelope s +
    BinarySmallUniformDescriptorLifetime.envelope (expressionHeightBudget s 13) + 72

theorem fromOriginalWithTrace_usage (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source)
    (hCase : source.w < (1-source.p)*source.ell)
    (s : ℕ) (hs : 3 ≤ s) (hH : source.FieldsHeight s) :
    usage (fromOriginalWithTrace input).2 ≤ envelope s := by
  let prepared := BinarySmallUniformPreparationLifetime.prepareWithTrace input
  let table := BinarySmallUniformDescriptorLifetime.descriptorWithTrace prepared.1
  have hPE := BinarySmallUniformPreparationLifetime.prepareWithTrace_erasure input hC
  have hPC : prepared.1.Canonical := by
    rw [hPE]
    exact BinarySmallUniformCompiler.prepare_canonical input hC
  have hPH : BinarySmallUniformFactoryWork.InputHeight prepared.1 (expressionHeightBudget s 13) := by
    rw [hPE]
    exact BinarySmallUniformFactoryWork.prepare_height input source hC hR hCase s (by omega) hH
  have hs13 : 3 ≤ expressionHeightBudget s 13 := hs.trans (expressionHeightBudget_ge_input s 13)
  have hPrep := BinarySmallUniformPreparationLifetime.prepareWithTrace_usage input source hC hR s (by omega) hH
  have hTable := BinarySmallUniformDescriptorLifetime.descriptorWithTrace_usage prepared.1 hPC _ hs13 hPH
  change usage prepared.2 ≤ _ at hPrep
  change usage table.2 ≤ _ at hTable
  have hw := wrap_usage 64 3 [prepared.2,table.2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change usage (wrap 64 3 [prepared.2,table.2]) ≤ _
  unfold envelope
  omega

theorem all_prefix (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source)
    (hCase : source.w < (1-source.p)*source.ell)
    (s : ℕ) (hs : 3 ≤ s) (hH : source.FieldsHeight s) (borrowed steps : ℕ) :
    retainedHeap borrowed (fromOriginalWithTrace input).2 steps ≤ borrowed + envelope s ∧
    framePeak ((fromOriginalWithTrace input).2.take steps) ≤ envelope s :=
  BinaryPRGHeapTraceUsage.all_prefix _ _
    (fromOriginalWithTrace_usage input source hC hR hCase s hs hH) borrowed steps

end Blotto.BinarySmallUniformFactoryLifetime
