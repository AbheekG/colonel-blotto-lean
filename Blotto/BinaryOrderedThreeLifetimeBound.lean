import Blotto.BinaryOrderedThreeLifetime

/-! Original ordered input heights derive complete regime, geometry and
selected-factory retained allocation/activation bounds, including E<=0. -/
namespace Blotto.BinaryOrderedThreeLifetimeBound
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGHeapTraceUsage BinaryThreeInputCompiler BinaryThreeGeometryLifetime BinarySyntaxUniformWork
set_option maxHeartbeats 2000000

def envelope (s : ℕ) : ℕ :=
  138 + regimeEnvelope s + comparisonEnvelope (2 * expressionHeightBudget s 2 + 1) + geometryEnvelope s +
    BinaryQuadraticThreeFactoryLifetime.bound (expressionHeightBudget s 2) +
    BinaryQuadraticThreeFactoryLifetime.frames (expressionHeightBudget s 2) + 4096 + 128

theorem regime_width (input : Input) (hC : input.Canonical) (s : ℕ) (hs : 3 ≤ s)
    (hHeight : BinaryOrderedThreeFactoryWork.InputHeight input s) :
    width (regimeWithTrace input.environment).1 ≤ 2 * expressionHeightBudget s 2 + 1 := by
  rw [regimeWithTrace_erasure input.environment (input_canonical input hC)]
  have hH := run_height_bound regime input.environment (input_canonical input hC) s 2 hs
    (BinaryOrderedThreeFactoryWork.environment_height input s hHeight) BinaryOrderedThreeFactoryWork.regime_sizes.1
  have hCan := regime.compile.run_canonical input.environment (input_canonical input hC) regime.compile_canonical
  have h := hCan.2.trans (rationalWordWidth_of_height hH)
  omega

theorem regular_usage (input : Input) (hC : input.Canonical) (s : ℕ) (hs : 3 ≤ s)
    (hHeight : BinaryOrderedThreeFactoryWork.InputHeight input s) :
    usage (BinaryQuadraticThreeFactoryLifetime.descriptorWithTrace (geometryWithTrace input.environment).1).2 ≤
      BinaryQuadraticThreeFactoryLifetime.bound (expressionHeightBudget s 2) +
        BinaryQuadraticThreeFactoryLifetime.frames (expressionHeightBudget s 2) := by
  rw [geometryWithTrace_erasure input.environment (input_canonical input hC)]
  have h := BinaryQuadraticThreeFactoryLifetime.descriptorWithTrace_bounds (geometryEnvironment input)
    (geometry_canonical input hC) (expressionHeightBudget s 2) (hs.trans (expressionHeightBudget_ge_input s 2))
    (BinaryOrderedThreeFactoryWork.geometry_height input hC s hs hHeight)
  unfold usage BinaryPRGHeapPrimitiveLifetime.cells
  exact Nat.add_le_add h.1 h.2

theorem descriptorWithTrace_usage (input : Input) (hC : input.Canonical) (s : ℕ) (hs : 3 ≤ s)
    (hHeight : BinaryOrderedThreeFactoryWork.InputHeight input s) :
    usage (BinaryOrderedThreeLifetime.descriptorWithTrace input).2 ≤ envelope s := by
  let environment := environmentWithTrace input
  let r := regimeWithTrace environment.1
  let compared := BinaryQuadraticExpressionLifetime.compareWithTrace r.1 BinaryRationalOpcode.zero
  let geometry := geometryWithTrace environment.1
  let child := BinaryQuadraticThreeFactoryLifetime.descriptorWithTrace geometry.1
  have hEnv := environmentWithTrace_usage input
  have hR := regimeWithTrace_usage input.environment (input_canonical input hC) s hs
    (BinaryOrderedThreeFactoryWork.environment_height input s hHeight)
  have hCompare := comparison_usage (regimeWithTrace input.environment).1 BinaryRationalOpcode.zero
    (2 * expressionHeightBudget s 2 + 1) (regime_width input hC s hs hHeight) (by change 1 ≤ _; omega)
  have hGeometry := geometryWithTrace_usage input.environment (input_canonical input hC) s hs
    (BinaryOrderedThreeFactoryWork.environment_height input s hHeight)
  have hChild := regular_usage input hC s hs hHeight
  have hExceptional := BinaryThreeReferenceLifetime.exceptionalWithTrace_usage input
  change usage environment.2 ≤ _ at hEnv
  change usage r.2 ≤ _ at hR
  change usage compared.2 ≤ _ at hCompare
  change usage geometry.2 ≤ _ at hGeometry
  change usage child.2 ≤ _ at hChild
  unfold BinaryOrderedThreeLifetime.descriptorWithTrace
  dsimp only
  split
  · have hw := wrap_usage 32 2 [environment.2,r.2,compared.2,geometry.2,child.2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change usage (wrap 32 2 [environment.2,r.2,compared.2,geometry.2,child.2]) ≤ _
    unfold envelope
    omega
  · have hw := wrap_usage 32 2 [environment.2,r.2,compared.2,(BinaryThreeReferenceLifetime.exceptionalWithTrace input).2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change usage (wrap 32 2 [environment.2,r.2,compared.2,(BinaryThreeReferenceLifetime.exceptionalWithTrace input).2]) ≤ _
    unfold envelope
    omega

theorem all_prefix (input : Input) (hC : input.Canonical) (s : ℕ) (hs : 3 ≤ s)
    (hHeight : BinaryOrderedThreeFactoryWork.InputHeight input s) (borrowed steps : ℕ) :
    retainedHeap borrowed (BinaryOrderedThreeLifetime.descriptorWithTrace input).2 steps ≤ borrowed + envelope s ∧
      framePeak ((BinaryOrderedThreeLifetime.descriptorWithTrace input).2.take steps) ≤ envelope s :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (descriptorWithTrace_usage input hC s hs hHeight) borrowed steps

end Blotto.BinaryOrderedThreeLifetimeBound
