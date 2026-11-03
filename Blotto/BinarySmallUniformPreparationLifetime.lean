import Blotto.BinaryFourSmallCoinLifetime
import Blotto.BinarySmallUniformFactoryWork
import Blotto.BinaryLifetimeUsage

/-! One actual eight-word parameter table supplies the three scale products
used by the small uniform branch. Source six-field heights bound every prefix. -/
namespace Blotto.BinarySmallUniformPreparationLifetime
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGHeapTraceUsage BinaryFactoryHeight BinaryLifetimeUsage
set_option maxHeartbeats 2000000

def prepareWithTrace (input : BinaryFourParameters.Input) : BinarySmallUniformCompiler.Input × Trace :=
  let parameters := BinaryReflectedParameterLifetime.prepareWithTrace input
  let first := BinaryQuadraticLifetime.applyWithTrace .mul (parameters.1.read 5) input.u
  let second := BinaryQuadraticLifetime.applyWithTrace .mul (parameters.1.read 5) input.v
  let third := BinaryQuadraticLifetime.applyWithTrace .mul (parameters.1.read 5) input.w
  (⟨input.B,first.1,second.1,third.1,input.ell⟩,
    wrap 48 4 [parameters.2,first.2,second.2,third.2])

theorem prepareWithTrace_erasure (input : BinaryFourParameters.Input) (hC : input.Canonical) :
    (prepareWithTrace input).1 = BinarySmallUniformCompiler.prepare input := by
  have hP := BinaryReflectedParameterLifetime.prepareWithTrace_erasure input hC
  have h5 : CanonicalWord ((BinaryReflectedParameterLifetime.prepareWithTrace input).1.read 5) := by
    rw [hP]
    exact BinaryFourParameters.prepare_canonical input hC 5
  unfold prepareWithTrace BinarySmallUniformCompiler.prepare
  dsimp only
  rw [BinaryQuadraticLifetime.applyWithTrace_state .mul _ input.u h5.1 hC.2.1.1,
    BinaryQuadraticLifetime.applyWithTrace_state .mul _ input.v h5.1 hC.2.2.1.1,
    BinaryQuadraticLifetime.applyWithTrace_state .mul _ input.w h5.1 hC.2.2.2.1.1,
    hP]

def envelope (s : ℕ) : ℕ :=
  BinaryReflectedParameterLifetime.envelope s +
    3 * opcodeEnvelope (2 * expressionHeightBudget s 12 + 1) + 80

theorem prepareWithTrace_usage (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source)
    (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s) :
    usage (prepareWithTrace input).2 ≤ envelope s := by
  let parameters := BinaryReflectedParameterLifetime.prepareWithTrace input
  let first := BinaryQuadraticLifetime.applyWithTrace .mul (parameters.1.read 5) input.u
  let second := BinaryQuadraticLifetime.applyWithTrace .mul (parameters.1.read 5) input.v
  let third := BinaryQuadraticLifetime.applyWithTrace .mul (parameters.1.read 5) input.w
  have hPE : parameters.1 = BinaryFourParameters.prepare input :=
    BinaryReflectedParameterLifetime.prepareWithTrace_erasure input hC
  have h5C : CanonicalWord (parameters.1.read 5) := by
    rw [hPE]
    exact BinaryFourParameters.prepare_canonical input hC 5
  have h5H : RationalHeight (value (parameters.1.read 5)) (expressionHeightBudget s 12) := by
    rw [hPE,BinaryFourParameters.prepare_value input source hC hR 5]
    exact hH.scalar hs 5
  have hm := expressionHeightBudget_ge_input s 12
  have hU : RationalHeight (value input.u) (expressionHeightBudget s 12) := by
    rw [hR.2.1]
    exact hH.2.1.mono hm
  have hV : RationalHeight (value input.v) (expressionHeightBudget s 12) := by
    rw [hR.2.2.1]
    exact hH.2.2.1.mono hm
  have hW : RationalHeight (value input.w) (expressionHeightBudget s 12) := by
    rw [hR.2.2.2.1]
    exact hH.2.2.2.1.mono hm
  have h5Width : width (parameters.1.read 5) ≤ 2 * expressionHeightBudget s 12 + 1 :=
    h5C.2.trans (by have h := rationalWordWidth_of_height h5H; omega)
  have hUWidth : width input.u ≤ 2 * expressionHeightBudget s 12 + 1 :=
    hC.2.1.2.trans (by have h := rationalWordWidth_of_height hU; omega)
  have hVWidth : width input.v ≤ 2 * expressionHeightBudget s 12 + 1 :=
    hC.2.2.1.2.trans (by have h := rationalWordWidth_of_height hV; omega)
  have hWWidth : width input.w ≤ 2 * expressionHeightBudget s 12 + 1 :=
    hC.2.2.2.1.2.trans (by have h := rationalWordWidth_of_height hW; omega)
  have hP := BinaryReflectedParameterLifetime.prepareWithTrace_usage input source hC hR s hs hH
  have hFirst := opcode_usage .mul (parameters.1.read 5) input.u
    (2 * expressionHeightBudget s 12 + 1) h5Width hUWidth
  have hSecond := opcode_usage .mul (parameters.1.read 5) input.v
    (2 * expressionHeightBudget s 12 + 1) h5Width hVWidth
  have hThird := opcode_usage .mul (parameters.1.read 5) input.w
    (2 * expressionHeightBudget s 12 + 1) h5Width hWWidth
  change usage parameters.2 ≤ _ at hP
  change usage first.2 ≤ _ at hFirst
  change usage second.2 ≤ _ at hSecond
  change usage third.2 ≤ _ at hThird
  have hw := wrap_usage 48 4 [parameters.2,first.2,second.2,third.2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change usage (wrap 48 4 [parameters.2,first.2,second.2,third.2]) ≤ _
  unfold envelope
  omega

theorem all_prefix (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source)
    (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s) (borrowed steps : ℕ) :
    retainedHeap borrowed (prepareWithTrace input).2 steps ≤ borrowed + envelope s ∧
    framePeak ((prepareWithTrace input).2.take steps) ≤ envelope s :=
  BinaryPRGHeapTraceUsage.all_prefix _ _
    (prepareWithTrace_usage input source hC hR s hs hH) borrowed steps

end Blotto.BinarySmallUniformPreparationLifetime
