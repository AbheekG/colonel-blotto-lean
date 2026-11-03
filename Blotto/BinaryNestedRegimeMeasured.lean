import Blotto.BinaryNestedOrderMeasured
import Blotto.BinaryNestedParameterMeasured
import Blotto.BinaryNestedRegimeLifetime

/-! Reached measured guards select a regime from the actual returned parameter
table. Full old data/trace is preserved; original fields derive all prices. -/
namespace Blotto.BinaryNestedRegimeMeasured
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
set_option autoImplicit false
set_option maxHeartbeats 600000

abbrev Input := BinaryNestedParameters.Input

def select (input : Input) (params : FixedArrayTable 9 SignedWord) : (Fin 3 × Trace) × ℕ :=
  let first := BinaryQuadraticExpressionMeasured.compare input.t (params.read 2)
  if first.1.1 then ((0,wrap 24 2 [first.1.2]),first.2+4) else
    let second := BinaryQuadraticExpressionMeasured.compare (params.read 1) input.t
    ((if second.1.1 then 1 else 2,wrap 24 2 [first.1.2,second.1.2]),first.2+second.2+8)

theorem select_erases (input : Input) (params : FixedArrayTable 9 SignedWord) :
    (select input params).1 = BinaryNestedRegimeLifetime.selectWithTrace input params := by
  simp only [select,BinaryNestedRegimeLifetime.selectWithTrace,BinaryQuadraticExpressionMeasured.compare_erases]
  split_ifs <;> rfl

def workEnvelope (W : ℕ) : ℕ := 2*BinaryQuadraticExpression.uniformPrice W+8

theorem select_bounds (input : Input) (params : FixedArrayTable 9 SignedWord) (W : ℕ)
    (hT : width input.t ≤ W) (hOne : width (params.read 1) ≤ W) (hTwo : width (params.read 2) ≤ W) :
    (select input params).2 ≤ workEnvelope W ∧ usage (select input params).1.2 ≤ BinaryNestedRegimeLifetime.envelope W := by
  constructor
  · let first := BinaryQuadraticExpressionMeasured.compare input.t (params.read 2)
    let second := BinaryQuadraticExpressionMeasured.compare (params.read 1) input.t
    have hFirst : first.2 ≤ BinaryQuadraticExpression.uniformPrice W := by
      rw [BinaryQuadraticExpressionMeasured.compare_work]
      exact BinaryQuadraticExpression.comparePrice_bound _ _ W (by omega) (by omega)
    have hSecond : second.2 ≤ BinaryQuadraticExpression.uniformPrice W := by
      rw [BinaryQuadraticExpressionMeasured.compare_work]
      exact BinaryQuadraticExpression.comparePrice_bound _ _ W (by omega) (by omega)
    unfold select
    dsimp only
    split
    · change first.2+4 ≤ _
      unfold workEnvelope
      omega
    · change first.2+second.2+8 ≤ _
      unfold workEnvelope
      omega
  · rw [select_erases]
    exact BinaryNestedRegimeLifetime.selectWithTrace_usage input params W hT hOne hTwo

def widthEnvelope (s : ℕ) : ℕ := 2*expressionHeightBudget s 16+1

theorem prepared_widths (input : Input) (params : FixedArrayTable 9 SignedWord) (hC : input.Canonical)
    (hParams : params = BinaryNestedProfileCompiler.parameters input) (s : ℕ) (hs : 3 ≤ s)
    (hH : BinaryNestedParameterWork.InputHeight input s) :
    width input.t ≤ widthEnvelope s ∧ width (params.read 1) ≤ widthEnvelope s ∧ width (params.read 2) ≤ widthEnvelope s := by
  have hm := expressionHeightBudget_ge_input s 16
  have hT : width input.t ≤ widthEnvelope s := by
    have h := hC.2.2.2.2.1.2.trans (rationalWordWidth_of_height hH.2.2.2.2.1)
    unfold widthEnvelope; omega
  have hP : ∀ j,width (params.read j) ≤ widthEnvelope s := by
    intro j
    rw [hParams]
    have h := (BinaryNestedProfileCompiler.parameters_canonical input hC j).2.trans
      (rationalWordWidth_of_height (BinaryNestedParameterWork.prepare_height input BinaryRationalOpcode.zero hC
        ⟨BinaryRationalOpcode.zero_valid,by decide⟩ s hs hH (BinaryFactoryHeight.zero_height s hs) j))
    unfold widthEnvelope; omega
  exact ⟨hT,hP 1,hP 2⟩

theorem prepared_bounds (input : Input) (params : FixedArrayTable 9 SignedWord) (hC : input.Canonical)
    (hParams : params = BinaryNestedProfileCompiler.parameters input) (s : ℕ) (hs : 3 ≤ s)
    (hH : BinaryNestedParameterWork.InputHeight input s) :
    (select input params).2 ≤ workEnvelope (widthEnvelope s) ∧
      usage (select input params).1.2 ≤ BinaryNestedRegimeLifetime.envelope (widthEnvelope s) := by
  have hW := prepared_widths input params hC hParams s hs hH
  exact select_bounds input params _ hW.1 hW.2.1 hW.2.2

theorem prepared_all_prefix (input : Input) (params : FixedArrayTable 9 SignedWord) (hC : input.Canonical)
    (hParams : params = BinaryNestedProfileCompiler.parameters input) (s : ℕ) (hs : 3 ≤ s)
    (hH : BinaryNestedParameterWork.InputHeight input s) (borrowed steps : ℕ) :
    retainedHeap borrowed (select input params).1.2 steps ≤ borrowed+BinaryNestedRegimeLifetime.envelope (widthEnvelope s) ∧
      framePeak ((select input params).1.2.take steps) ≤ BinaryNestedRegimeLifetime.envelope (widthEnvelope s) :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (prepared_bounds input params hC hParams s hs hH).2 borrowed steps

end Blotto.BinaryNestedRegimeMeasured
