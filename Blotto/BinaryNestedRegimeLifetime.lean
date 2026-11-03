import Blotto.BinaryNestedInteriorPrefixLifetime

/-! Actual ordered-interior regime tests consume the shared parameter table.
The first guard selects t≤v; only its false branch tests u≤t. -/
namespace Blotto.BinaryNestedRegimeLifetime
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGHeapTraceUsage
set_option maxHeartbeats 2000000

abbrev Input := BinaryNestedParameters.Input

def selectWithTrace (input : Input) (params : FixedArrayTable 9 SignedWord) : Fin 3 × Trace :=
  let first := BinaryQuadraticExpressionLifetime.compareWithTrace input.t (params.read 2)
  if first.1 then (0,wrap 24 2 [first.2]) else
    let second := BinaryQuadraticExpressionLifetime.compareWithTrace (params.read 1) input.t
    (if second.1 then 1 else 2,wrap 24 2 [first.2,second.2])

def oldSelect (input : Input) (params : FixedArrayTable 9 SignedWord) : Fin 3 :=
  if BinaryRationalArithmetic.lessEqual input.t (params.read 2) then 0
  else if BinaryRationalArithmetic.lessEqual (params.read 1) input.t then 1 else 2

theorem selectWithTrace_erasure (input : Input) (params : FixedArrayTable 9 SignedWord) :
    (selectWithTrace input params).1 = oldSelect input params := by
  unfold selectWithTrace oldSelect
  simp only [BinaryQuadraticExpressionLifetime.compareWithTrace_erases]
  split
  · rfl
  · split <;> rfl

def envelope (W : ℕ) : ℕ :=
  2 * BinaryThreeGeometryLifetime.comparisonEnvelope W + 64

theorem selectWithTrace_usage (input : Input) (params : FixedArrayTable 9 SignedWord)
    (W : ℕ) (hT : width input.t ≤ W)
    (hOne : width (params.read 1) ≤ W) (hTwo : width (params.read 2) ≤ W) :
    usage (selectWithTrace input params).2 ≤ envelope W := by
  let first := BinaryQuadraticExpressionLifetime.compareWithTrace input.t (params.read 2)
  let second := BinaryQuadraticExpressionLifetime.compareWithTrace (params.read 1) input.t
  have hFirst := BinaryThreeGeometryLifetime.comparison_usage input.t (params.read 2) W hT hTwo
  have hSecond := BinaryThreeGeometryLifetime.comparison_usage (params.read 1) input.t W hOne hT
  change usage first.2 ≤ _ at hFirst
  change usage second.2 ≤ _ at hSecond
  unfold selectWithTrace
  dsimp only
  split
  · have hw := wrap_usage 24 2 [first.2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change usage (wrap 24 2 [first.2]) ≤ _
    unfold envelope
    omega
  · have hw := wrap_usage 24 2 [first.2,second.2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change usage (wrap 24 2 [first.2,second.2]) ≤ _
    unfold envelope
    omega

theorem prepared_usage (input : Input) (hC : input.Canonical) (s : ℕ) (hs : 3 ≤ s)
    (hH : BinaryNestedParameterWork.InputHeight input s) :
    usage (selectWithTrace input (BinaryNestedParameterLifetime.prepareWithTrace input).1).2 ≤
      envelope (2 * expressionHeightBudget s 16 + 1) := by
  let W := 2 * expressionHeightBudget s 16 + 1
  have hT : width input.t ≤ W := by
    have h := hC.2.2.2.2.1.2.trans (rationalWordWidth_of_height hH.2.2.2.2.1)
    have hm := expressionHeightBudget_ge_input s 16
    dsimp only [W]
    omega
  have hParams := BinaryNestedParameterLifetime.prepareWithTrace_erasure input hC
  have hOne : width ((BinaryNestedParameterLifetime.prepareWithTrace input).1.read 1) ≤ W := by
    rw [hParams]
    have h := (BinaryNestedProfileCompiler.parameters_canonical input hC 1).2.trans
      (rationalWordWidth_of_height (BinaryNestedParameterWork.prepare_height input BinaryRationalOpcode.zero
        hC ⟨BinaryRationalOpcode.zero_valid,by decide⟩ s hs hH
        (BinaryFactoryHeight.zero_height s hs) 1))
    dsimp only [W]
    omega
  have hTwo : width ((BinaryNestedParameterLifetime.prepareWithTrace input).1.read 2) ≤ W := by
    rw [hParams]
    have h := (BinaryNestedProfileCompiler.parameters_canonical input hC 2).2.trans
      (rationalWordWidth_of_height (BinaryNestedParameterWork.prepare_height input BinaryRationalOpcode.zero
        hC ⟨BinaryRationalOpcode.zero_valid,by decide⟩ s hs hH
        (BinaryFactoryHeight.zero_height s hs) 2))
    dsimp only [W]
    omega
  exact selectWithTrace_usage input _ W hT hOne hTwo

theorem all_prefix (input : Input) (params : FixedArrayTable 9 SignedWord)
    (W : ℕ) (hT : width input.t ≤ W)
    (hOne : width (params.read 1) ≤ W) (hTwo : width (params.read 2) ≤ W)
    (borrowed steps : ℕ) :
    retainedHeap borrowed (selectWithTrace input params).2 steps ≤ borrowed + envelope W ∧
    framePeak ((selectWithTrace input params).2.take steps) ≤ envelope W :=
  BinaryPRGHeapTraceUsage.all_prefix _ _
    (selectWithTrace_usage input params W hT hOne hTwo) borrowed steps

end Blotto.BinaryNestedRegimeLifetime
