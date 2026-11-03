import Blotto.BinaryNormalizedCoordinate
import Blotto.BinaryLifetimeArrayExtras
import Blotto.BinaryPlannedQuadratic
import Blotto.BinaryFourParametersMeasured
import Blotto.BinarySmallUniformSplitMeasured

/-! One returned measured parameter table supplies all three measured scale
products. The actual prepared words, work and enlarged trace are retained.
Original fields derive the bound; native model realization remains separate. -/
namespace Blotto.BinarySmallUniformPreparationMeasured
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGHeapTraceUsage BinaryFactoryHeight BinaryLifetimeUsage
set_option autoImplicit false
attribute [local irreducible] BinaryPlannedQuadratic.apply BinaryPlannedQuadratic.applyMeasured
set_option maxHeartbeats 500000

theorem opcode_bounds (op : RealArithmeticOp) (a b : SignedWord)
    (hA : CanonicalWord a) (hB : CanonicalWord b) (s : ℕ)
    (ha : RationalHeight (value a) s) (hb : RationalHeight (value b) s) :
    (BinaryQuadraticMeasured.apply op a b).2 ≤ BinarySmallUniformSplitMeasured.opcodePrice s ∧
      usage (BinaryQuadraticMeasured.apply op a b).1.2 ≤ opcodeEnvelope (2*s+1) := by
  refine ⟨BinarySmallUniformSplitMeasured.opcode_work op a b hA hB s ha hb,?_⟩
  have hWA : width a ≤ 2*s+1 := by have h := hA.2.trans (rationalWordWidth_of_height ha); omega
  have hWB : width b ≤ 2*s+1 := by have h := hB.2.trans (rationalWordWidth_of_height hb); omega
  rw [BinaryQuadraticMeasured.apply_erases]
  exact opcode_usage op a b (2*s+1) hWA hWB

def collect (input : BinaryFourParameters.Input) (parameters : (FixedArrayTable 8 SignedWord × Trace) × ℕ)
    (first second third : (SignedWord × Trace) × ℕ) : (BinarySmallUniformCompiler.Input × Trace) × ℕ :=
  ((⟨input.B,first.1.1,second.1.1,third.1.1,input.ell⟩,
    wrap 48 4 [parameters.1.2,first.1.2,second.1.2,third.1.2]),parameters.2+first.2+second.2+third.2+12)

set_option cleanup.letToHave false in
def prepareWithExtras (input : BinaryFourParameters.Input) : ((BinarySmallUniformCompiler.Input × Trace) × ℕ) × ℕ :=
  let parameters := BinaryFourParametersMeasured.prepareWithExtras input
  let first := BinaryNormalizedCoordinate.opcode .mul (parameters.1.1.1.read 5) input.u
  let second := BinaryNormalizedCoordinate.opcode .mul (parameters.1.1.1.read 5) input.v
  let third := BinaryNormalizedCoordinate.opcode .mul (parameters.1.1.1.read 5) input.w
  (collect input parameters.1 first.1 second.1 third.1,parameters.2+first.2+second.2+third.2)

def prepare (input : BinaryFourParameters.Input) : (BinarySmallUniformCompiler.Input × Trace) × ℕ :=
  (prepareWithExtras input).1

theorem prepareWithExtras_compat (input : BinaryFourParameters.Input) :
    (prepareWithExtras input).1 = prepare input := rfl

theorem prepare_record (input : BinaryFourParameters.Input) :
    prepare input =
  let parameters := BinaryFourParametersMeasured.prepare input
  let first := BinaryPlannedQuadratic.apply .mul (parameters.1.1.read 5) input.u
  let second := BinaryPlannedQuadratic.apply .mul (parameters.1.1.read 5) input.v
  let third := BinaryPlannedQuadratic.apply .mul (parameters.1.1.read 5) input.w
  collect input parameters first second third := by
  simp only [prepare,prepareWithExtras,BinaryLifetimeArrayExtras.build_record,BinaryNormalizedCoordinate.opcode_record,BinaryFourParametersMeasured.prepareWithExtras_compat]

theorem prepare_eq (input : BinaryFourParameters.Input) : prepare input =
    let parameters := BinaryFourParametersMeasured.prepare input
    collect input parameters
      (BinaryQuadraticMeasured.apply .mul (parameters.1.1.read 5) input.u)
      (BinaryQuadraticMeasured.apply .mul (parameters.1.1.read 5) input.v)
      (BinaryQuadraticMeasured.apply .mul (parameters.1.1.read 5) input.w) := by
  simp only [prepare_record,BinaryPlannedQuadratic.apply_previous]

theorem prepare_data (input : BinaryFourParameters.Input) :
    (prepare input).1.1 = (BinarySmallUniformPreparationLifetime.prepareWithTrace input).1 := by
  simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,prepare_record,collect,BinarySmallUniformPreparationLifetime.prepareWithTrace,
    BinaryFourParametersMeasured.prepare_data,BinaryQuadraticMeasured.apply_erases]

def workEnvelope (s : ℕ) : ℕ := BinaryFourParametersMeasured.workEnvelope s+
  3*BinarySmallUniformSplitMeasured.opcodePrice (expressionHeightBudget s 12)+12

def envelope (s : ℕ) : ℕ := BinaryFourParametersMeasured.envelope s+
  3*opcodeEnvelope (2*expressionHeightBudget s 12+1)+80

theorem collect_bounds (input : BinaryFourParameters.Input) (parameters : (FixedArrayTable 8 SignedWord × Trace) × ℕ)
    (first second third : (SignedWord × Trace) × ℕ) (P M B U : ℕ)
    (hp : parameters.2 ≤ P ∧ usage parameters.1.2 ≤ B)
    (hf : first.2 ≤ M ∧ usage first.1.2 ≤ U) (hs : second.2 ≤ M ∧ usage second.1.2 ≤ U)
    (ht : third.2 ≤ M ∧ usage third.1.2 ≤ U) :
    (collect input parameters first second third).2 ≤ P+3*M+12 ∧
      usage (collect input parameters first second third).1.2 ≤ B+3*U+80 := by
  have hw := wrap_usage 48 4 [parameters.1.2,first.1.2,second.1.2,third.1.2]
  simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change parameters.2+first.2+second.2+third.2+12 ≤ _ ∧ usage (wrap 48 4 [parameters.1.2,first.1.2,second.1.2,third.1.2]) ≤ _
  exact ⟨by omega,by omega⟩

theorem prepare_bounds (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s) :
    (prepare input).2 ≤ workEnvelope s ∧ usage (prepare input).1.2 ≤ envelope s := by
  let parameters := BinaryFourParametersMeasured.prepare input
  let first := BinaryQuadraticMeasured.apply .mul (parameters.1.1.read 5) input.u
  let second := BinaryQuadraticMeasured.apply .mul (parameters.1.1.read 5) input.v
  let third := BinaryQuadraticMeasured.apply .mul (parameters.1.1.read 5) input.w
  have hPE : parameters.1.1 = BinaryFourParameters.prepare input :=
    (BinaryFourParametersMeasured.prepare_data input).trans (BinaryReflectedParameterLifetime.prepareWithTrace_erasure input hC)
  have h5C : CanonicalWord (parameters.1.1.read 5) := by
    rw [hPE]
    exact BinaryFourParameters.prepare_canonical input hC 5
  have h5H : RationalHeight (value (parameters.1.1.read 5)) (expressionHeightBudget s 12) := by
    rw [hPE,BinaryFourParameters.prepare_value input source hC hR 5]
    exact hH.scalar hs 5
  have hm := expressionHeightBudget_ge_input s 12
  have hU : RationalHeight (value input.u) (expressionHeightBudget s 12) := by rw [hR.2.1]; exact hH.2.1.mono hm
  have hV : RationalHeight (value input.v) (expressionHeightBudget s 12) := by rw [hR.2.2.1]; exact hH.2.2.1.mono hm
  have hW : RationalHeight (value input.w) (expressionHeightBudget s 12) := by rw [hR.2.2.2.1]; exact hH.2.2.2.1.mono hm
  have hP := BinaryFourParametersMeasured.prepare_bounds input source hC hR s hs hH
  have hFirst := opcode_bounds .mul (parameters.1.1.read 5) input.u h5C hC.2.1 _ h5H hU
  have hSecond := opcode_bounds .mul (parameters.1.1.read 5) input.v h5C hC.2.2.1 _ h5H hV
  have hThird := opcode_bounds .mul (parameters.1.1.read 5) input.w h5C hC.2.2.2.1 _ h5H hW
  change parameters.2 ≤ _ ∧ usage parameters.1.2 ≤ _ at hP
  change first.2 ≤ _ ∧ usage first.1.2 ≤ _ at hFirst
  change second.2 ≤ _ ∧ usage second.1.2 ≤ _ at hSecond
  change third.2 ≤ _ ∧ usage third.1.2 ≤ _ at hThird
  have hResult := collect_bounds input parameters first second third _ _ _ _ hP hFirst hSecond hThird
  rw [prepare_eq]
  simpa only [parameters,first,second,third,workEnvelope,envelope] using hResult

theorem all_prefix (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s)
    (borrowed steps : ℕ) :
    retainedHeap borrowed (prepare input).1.2 steps ≤ borrowed+envelope s ∧
      framePeak ((prepare input).1.2.take steps) ≤ envelope s :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (prepare_bounds input source hC hR s hs hH).2 borrowed steps

end Blotto.BinarySmallUniformPreparationMeasured
