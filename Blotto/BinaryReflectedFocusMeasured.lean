import Blotto.BinaryQuadraticExpressionMeasured
import Blotto.BinaryReflectedFocusLifetime

/-! Actual measured signed comparisons choose the reached fractional focus.
Full preceding data/trace is retained; source resource/capacity widths and then
original fields derive work. Native observers/references remain separate. -/
namespace Blotto.BinaryReflectedFocusMeasured
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
set_option autoImplicit false
set_option maxHeartbeats 500000

def fractional (capacity resource : FixedArrayTable 3 SignedWord) (j : Fin 3) : (Bool × Trace) × ℕ :=
  let positive := BinaryQuadraticExpressionMeasured.compare (resource.read j) BinaryRationalOpcode.zero
  let below := BinaryQuadraticExpressionMeasured.compare (capacity.read j) (resource.read j)
  (((!positive.1.1) && (!below.1.1),wrap 12 2 [positive.1.2,below.1.2]),positive.2+below.2+8)

theorem fractional_erases (capacity resource : FixedArrayTable 3 SignedWord) (j : Fin 3) :
    (fractional capacity resource j).1 = BinaryReflectedFocusLifetime.fractionalWithTrace capacity resource j := by
  simp only [fractional,BinaryReflectedFocusLifetime.fractionalWithTrace,BinaryQuadraticExpressionMeasured.compare_erases]

def fractionalPrice (W : ℕ) : ℕ := 2*BinaryQuadraticExpression.uniformPrice W+8

theorem fractional_work (capacity resource : FixedArrayTable 3 SignedWord) (j : Fin 3)
    (W : ℕ) (hW : 1 ≤ W) (hCap : width (capacity.read j) ≤ W) (hResource : width (resource.read j) ≤ W) :
    (fractional capacity resource j).2 ≤ fractionalPrice W := by
  have hZero : width BinaryRationalOpcode.zero ≤ W := hW
  have hPositive := BinaryQuadraticExpression.comparePrice_bound (resource.read j) BinaryRationalOpcode.zero W (by omega) (by omega)
  have hBelow := BinaryQuadraticExpression.comparePrice_bound (capacity.read j) (resource.read j) W (by omega) (by omega)
  simp only [fractional,BinaryQuadraticExpressionMeasured.compare_work,fractionalPrice]
  omega

def focus (capacity resource : FixedArrayTable 3 SignedWord) : (Fin 3 × Trace) × ℕ :=
  let first := fractional capacity resource 0
  if first.1.1 then ((0,wrap 12 2 [first.1.2]),first.2+4) else
    let second := fractional capacity resource 1
    ((if second.1.1 then 1 else 2,wrap 12 2 [first.1.2,second.1.2]),first.2+second.2+8)

theorem focus_erases (capacity resource : FixedArrayTable 3 SignedWord) :
    (focus capacity resource).1 = BinaryReflectedFocusLifetime.focusWithTrace capacity resource := by
  simp only [focus,BinaryReflectedFocusLifetime.focusWithTrace,fractional_erases]
  split_ifs <;> rfl

def focusPrice (W : ℕ) : ℕ := 2*fractionalPrice W+8

theorem focus_work (capacity resource : FixedArrayTable 3 SignedWord)
    (W : ℕ) (hW : 1 ≤ W) (hCap : ∀ j,width (capacity.read j) ≤ W) (hResource : ∀ j,width (resource.read j) ≤ W) :
    (focus capacity resource).2 ≤ focusPrice W := by
  have hFirst := fractional_work capacity resource 0 W hW (hCap 0) (hResource 0)
  have hSecond := fractional_work capacity resource 1 W hW (hCap 1) (hResource 1)
  unfold focus
  dsimp only
  split <;> unfold focusPrice <;> omega

def preparedFocus {input : BinaryFourParameters.Input} (prepared : BinaryReflectedPreparationLifetime.Prepared input)
    (state : BinaryThreeResourceState.State) : (Fin 3 × Trace) × ℕ := focus prepared.capacity state.resource

theorem preparedFocus_erases {input : BinaryFourParameters.Input} (prepared : BinaryReflectedPreparationLifetime.Prepared input)
    (state : BinaryThreeResourceState.State) :
    (preparedFocus prepared state).1 = BinaryReflectedFocusLifetime.preparedFocusWithTrace prepared state :=
  focus_erases _ _

theorem reached_work (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1-source.p)*source.ell)
    (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s) (N : ℕ) (bits : Fin N → Bool)
    (result : BinaryThreeResourcePair.Certified (BinaryReflectedFourSetup.prepare input).capacity)
    (hSuccess : (BinarySharedResourceRun.setupRun input hC N bits).1 = some result)
    (prepared : BinaryReflectedPreparationLifetime.Prepared input) :
    (preparedFocus prepared result.state).2 ≤ focusPrice (2*expressionHeightBudget s 21+1) := by
  have hWidths := BinaryReflectedFocusLifetime.prepared_reached_widths input source hC hR hCase s hs hH N bits result hSuccess prepared
  exact focus_work _ _ _ (by omega) hWidths.1 hWidths.2

theorem reached_all_prefix (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1-source.p)*source.ell)
    (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s) (N : ℕ) (bits : Fin N → Bool)
    (result : BinaryThreeResourcePair.Certified (BinaryReflectedFourSetup.prepare input).capacity)
    (hSuccess : (BinarySharedResourceRun.setupRun input hC N bits).1 = some result)
    (prepared : BinaryReflectedPreparationLifetime.Prepared input) (borrowed steps : ℕ) :
    retainedHeap borrowed (preparedFocus prepared result.state).1.2 steps ≤
      borrowed+BinaryReflectedFocusLifetime.focusEnvelope (2*expressionHeightBudget s 21+1) ∧
    framePeak ((preparedFocus prepared result.state).1.2.take steps) ≤
      BinaryReflectedFocusLifetime.focusEnvelope (2*expressionHeightBudget s 21+1) := by
  rw [preparedFocus_erases]
  exact BinaryPRGHeapTraceUsage.all_prefix _ _
    (BinaryReflectedFocusLifetime.preparedFocusWithTrace_reached_usage input source hC hR hCase s hs hH N bits result hSuccess prepared)
    borrowed steps

end Blotto.BinaryReflectedFocusMeasured
