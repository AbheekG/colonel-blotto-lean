import Blotto.BinaryLifetimeArrayExtras
import Blotto.BinarySmallUniformDescriptorMeasured
import Blotto.BinarySmallUniformFactoryLifetime

/-! The actual measured scale preparation feeds the complete measured merged
factory. Original six-field heights price the reached small-uniform branch.
Exact preceding descriptor data is preserved; native model costs remain. -/
namespace Blotto.BinarySmallUniformFactoryMeasured
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
set_option autoImplicit false
set_option maxHeartbeats 500000

def collect (prepared : (BinarySmallUniformCompiler.Input × Trace) × ℕ)
    (table : (BinaryStoredOverlapEnvironment.Segment 4 9 × Trace) × ℕ) :
    (BinaryStoredOverlapEnvironment.Segment 4 9 × Trace) × ℕ :=
  ((table.1.1,wrap 64 3 [prepared.1.2,table.1.2]),prepared.2+table.2+8)

set_option cleanup.letToHave false in
def descriptorWithExtras (input : BinaryFourParameters.Input) : ((BinaryStoredOverlapEnvironment.Segment 4 9 × Trace) × ℕ) × ℕ :=
  let prepared := BinarySmallUniformPreparationMeasured.prepareWithExtras input
  let table := BinarySmallUniformDescriptorMeasured.descriptorWithExtras prepared.1.1.1
  (collect prepared.1 table.1,prepared.2+table.2)

def descriptor (input : BinaryFourParameters.Input) : (BinaryStoredOverlapEnvironment.Segment 4 9 × Trace) × ℕ :=
  (descriptorWithExtras input).1

theorem descriptorWithExtras_compat (input : BinaryFourParameters.Input) :
    (descriptorWithExtras input).1 = descriptor input := rfl

theorem descriptor_record (input : BinaryFourParameters.Input) :
    descriptor input =
  let prepared := BinarySmallUniformPreparationMeasured.prepare input
  let table := BinarySmallUniformDescriptorMeasured.descriptor prepared.1.1
  collect prepared table := by
  simp only [descriptor,descriptorWithExtras,BinaryLifetimeArrayExtras.build_record,BinarySmallUniformDescriptorMeasured.childWithExtras_compat,BinarySmallUniformDescriptorMeasured.descriptorWithExtras_compat,BinarySmallUniformPreparationMeasured.prepareWithExtras_compat]

theorem descriptor_eq (input : BinaryFourParameters.Input) : descriptor input =
    collect (BinarySmallUniformPreparationMeasured.prepare input)
      (BinarySmallUniformDescriptorMeasured.descriptor (BinarySmallUniformPreparationMeasured.prepare input).1.1) := by
  exact descriptor_record input

theorem descriptor_data (input : BinaryFourParameters.Input) :
    (descriptor input).1.1 = (BinarySmallUniformFactoryLifetime.fromOriginalWithTrace input).1 := by
  simp only [descriptor_record,collect,BinarySmallUniformFactoryLifetime.fromOriginalWithTrace,
    BinarySmallUniformPreparationMeasured.prepare_data,BinarySmallUniformDescriptorMeasured.descriptor_data]

def workEnvelope (s : ℕ) : ℕ := BinarySmallUniformPreparationMeasured.workEnvelope s+
  BinarySmallUniformDescriptorMeasured.workEnvelope (expressionHeightBudget s 13)+8

def envelope (s : ℕ) : ℕ := BinarySmallUniformPreparationMeasured.envelope s+
  BinarySmallUniformDescriptorMeasured.envelope (expressionHeightBudget s 13)+72

theorem collect_bounds (prepared : (BinarySmallUniformCompiler.Input × Trace) × ℕ)
    (table : (BinaryStoredOverlapEnvironment.Segment 4 9 × Trace) × ℕ) (P T B C : ℕ)
    (hp : prepared.2 ≤ P ∧ usage prepared.1.2 ≤ B) (ht : table.2 ≤ T ∧ usage table.1.2 ≤ C) :
    (collect prepared table).2 ≤ P+T+8 ∧ usage (collect prepared table).1.2 ≤ B+C+72 := by
  have hw := wrap_usage 64 3 [prepared.1.2,table.1.2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change prepared.2+table.2+8 ≤ _ ∧ usage (wrap 64 3 [prepared.1.2,table.1.2]) ≤ _
  exact ⟨by omega,by omega⟩

theorem descriptor_bounds (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1-source.p)*source.ell)
    (s : ℕ) (hs : 3 ≤ s) (hH : source.FieldsHeight s) :
    (descriptor input).2 ≤ workEnvelope s ∧ usage (descriptor input).1.2 ≤ envelope s := by
  let prepared := BinarySmallUniformPreparationMeasured.prepare input
  let table := BinarySmallUniformDescriptorMeasured.descriptor prepared.1.1
  have hPE := (BinarySmallUniformPreparationMeasured.prepare_data input).trans
    (BinarySmallUniformPreparationLifetime.prepareWithTrace_erasure input hC)
  have hPC : prepared.1.1.Canonical := by rw [hPE]; exact BinarySmallUniformCompiler.prepare_canonical input hC
  have hPH : BinarySmallUniformFactoryWork.InputHeight prepared.1.1 (expressionHeightBudget s 13) := by
    rw [hPE]
    exact BinarySmallUniformFactoryWork.prepare_height input source hC hR hCase s (by omega) hH
  have hs13 : 3 ≤ expressionHeightBudget s 13 := hs.trans (expressionHeightBudget_ge_input s 13)
  have hPrep := BinarySmallUniformPreparationMeasured.prepare_bounds input source hC hR s (by omega) hH
  have hTable := BinarySmallUniformDescriptorMeasured.descriptor_bounds prepared.1.1 hPC _ hs13 hPH
  have hResult := collect_bounds prepared table _ _ _ _ hPrep hTable
  rw [descriptor_eq]
  simpa only [prepared,table,workEnvelope,envelope] using hResult

theorem all_prefix (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1-source.p)*source.ell)
    (s : ℕ) (hs : 3 ≤ s) (hH : source.FieldsHeight s) (borrowed steps : ℕ) :
    retainedHeap borrowed (descriptor input).1.2 steps ≤ borrowed+envelope s ∧
      framePeak ((descriptor input).1.2.take steps) ≤ envelope s :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (descriptor_bounds input source hC hR hCase s hs hH).2 borrowed steps

end Blotto.BinarySmallUniformFactoryMeasured
