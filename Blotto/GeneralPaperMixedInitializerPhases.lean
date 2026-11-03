import Blotto.GeneralPaperMixedInitializerControls

/-! Every actual A-priced initializer phase at physical width S. The two
borrowed word references in the parsed return are counted explicitly. -/
namespace Blotto.GeneralPaperMixedInitializerPhases
open GeneralPaperEqualInputDomain
open GeneralPaperEqualInputInitializerLifetime (Phase valueWords budgetWords numeratorWords denominatorWords accuracySum)
open GeneralPaperEqualInputInitializerLifetime (value_data budget_data numerator_data denominator_data accuracy_data)
set_option autoImplicit false
set_option maxHeartbeats 4500000
set_option maxRecDepth 16384

def component (model : RationalCostModel) (S A K : ℕ) (p : Input model) : Phase p.n → ℕ
  | .accuracy => GeneralPaperMixedBinaryAccuracyStorage.window S A p.words
  | .indices cursor _ => GeneralPaperPackingAllocationLifetime.indicesLive S p.n cursor
  | .values _ _ => GeneralPaperMixedValueLengthStorage.window model S A p.values 0
  | .budget => GeneralPaperMixedRationalLengthStorage.footprint model S A p.budget
  | .numerator => GeneralPaperMixedAccuracyCountStorage.window S A p.words.numerator.bits
  | .denominator => GeneralPaperMixedAccuracyCountStorage.window S A p.words.denominator.bits
  | .sum => GeneralPaperMixedPrimitiveStorage.scalarFoot model S A (numeratorWords model A p).1
      (denominatorWords model A p).1 (accuracySum model A p).1
  | .word => GeneralPaperMixedReferenceWordStorage.footprint model S A K p.n p.k
      (valueWords model A p).1 (budgetWords model A p).1 (accuracySum model A p).1
  | .returned => GeneralPaperMixedInitializerControls.returnedOwner model S A K p

theorem sum_bound (model : RationalCostModel) (S A : ℕ) (h : A ≤ S) (p : Input model) :
    GeneralPaperMixedPrimitiveStorage.scalarFoot model S A (numeratorWords model A p).1
      (denominatorWords model A p).1 (accuracySum model A p).1 ≤
      GeneralPaperEqualInputInitializerLifetime.sumProfile model S (accuracySize p) := by
  have hs := GeneralPaperEqualInputInitializerLifetime.sum_bound model S p
  simp only [numerator_data, denominator_data] at hs
  change GeneralPaperMixedPrimitiveStorage.scalarFoot model S S p.words.numerator.width p.words.denominator.width
    (p.words.numerator.width + p.words.denominator.width) ≤ _ at hs
  have hm := GeneralPaperMixedPrimitiveStorage.scalar_le_diagonal model S A p.words.numerator.width p.words.denominator.width
    (p.words.numerator.width + p.words.denominator.width) h
  simpa only [accuracySum, numerator_data, denominator_data, GeneralPaperNaturalScalarStep.data,
    GeneralPaperNaturalScalarStep.Op.apply] using hm.trans hs

theorem component_bound (model : RationalCostModel) (S A K : ℕ) (h : A ≤ S) (p : Input model) (phase : Phase p.n) :
    component model S A K p phase ≤ GeneralPaperEqualInputInitializerLifetime.scratchProfile model S K p + 2 * S := by
  have hAcc := GeneralPaperMixedBinaryAccuracyStorage.bounded S A h p.words
  change GeneralPaperMixedBinaryAccuracyStorage.window S A p.words ≤ GeneralPaperBinaryAccuracyConstructionStorage.profile S (accuracySize p) at hAcc
  have hIndices := GeneralPaperPackingAllocationLifetime.indices_bound S p.n
  have hValues := GeneralPaperMixedValueLengthStorage.bounded model S A h p.values 0
  have hBudget := GeneralPaperMixedRationalLengthStorage.input_bound model S A h p.budget
  have hNum := GeneralPaperMixedAccuracyCountStorage.bounded S A (accuracySize p) h p.words.numerator.bits (by
    simp only [PositiveBinaryWord.bits, List.length_cons]
    unfold accuracySize GeneralPaperBinaryAccuracyConstructionStorage.inputSize PositiveBinaryWord.width
    omega)
  have hDen := GeneralPaperMixedAccuracyCountStorage.bounded S A (accuracySize p) h p.words.denominator.bits (by
    simp only [PositiveBinaryWord.bits, List.length_cons]
    unfold accuracySize GeneralPaperBinaryAccuracyConstructionStorage.inputSize PositiveBinaryWord.width
    omega)
  have hSum := sum_bound model S A h p
  have hWord := GeneralPaperMixedReferenceWordStorage.bounded model S A K p.n p.k
    (valueWords model A p).1 (budgetWords model A p).1 (accuracySum model A p).1 h
  simp only [value_data, budget_data, accuracy_data] at hWord
  have hReturn := GeneralPaperMixedInitializerControls.returned_bound model S A K h p
  change GeneralPaperMixedValueLengthStorage.window model S A p.values 0 ≤
    GeneralPaperValueInputLengthLifetime.profile model S p.n (originalSize p) 0 at hValues
  change GeneralPaperMixedRationalLengthStorage.footprint model S A p.budget ≤
    GeneralPaperWordLengthLifetime.rationalProfile model S (budgetSize p) at hBudget
  cases phase with
  | indices cursor hc =>
    have hi := hIndices cursor hc
    simp only [component]
    unfold GeneralPaperEqualInputInitializerLifetime.scratchProfile
    omega
  | word =>
    simp only [component, value_data, budget_data, accuracy_data]
    unfold GeneralPaperEqualInputInitializerLifetime.scratchProfile
    omega
  | _ =>
    simp only [component]
    unfold GeneralPaperEqualInputInitializerLifetime.scratchProfile
    all_goals omega

def window (model : RationalCostModel) (S A K : ℕ) (p : Input model) (phase : Phase p.n) : ℕ :=
  GeneralPaperEqualInputInitializerLifetime.inputOwner model S p +
    GeneralPaperMixedInitializerControls.controls model S A K p +
    GeneralPaperEqualInputInitializerLifetime.cursorControls S phase + component model S A K p phase

def profile (model : RationalCostModel) (S K : ℕ) (p : Input model) : ℕ :=
  GeneralPaperEqualInputInitializerLifetime.profile model S K p + 2 * S

theorem all_phases (model : RationalCostModel) (S A K : ℕ) (h : A ≤ S) (p : Input model) (phase : Phase p.n) :
    window model S A K p phase ≤ profile model S K p := by
  have hi := GeneralPaperEqualInputInitializerLifetime.input_bound model S p
  have hc := GeneralPaperMixedInitializerControls.controls_bound model S A K h p
  have hx := GeneralPaperEqualInputInitializerLifetime.cursor_bound S p.n phase
  have hs := component_bound model S A K h p phase
  unfold window profile GeneralPaperEqualInputInitializerLifetime.profile
  omega

theorem original_return_fields (model : RationalCostModel) (S A K : ℕ) (p : GeneralPaperOriginalGameInput.Input) :
    let actual := GeneralPaperOriginalMeasuredReference.prepare model A K p
    GeneralPaperEncodedScalarStorage.fields S [actual.1.1.exponent, actual.1.2, actual.2] + 64 * S + 2 * S =
      GeneralPaperMixedInitializerControls.returnedOwner model S A K (GeneralPaperOriginalGameInput.equalInput model p) := rfl

theorem original_phases (model : RationalCostModel) (K : ℕ) (hK : 1 ≤ K) (p : GeneralPaperOriginalGameInput.Input) :
    let S := (GeneralPaperOriginalMeasuredReference.prepare model 1 K p).1.2
    ∀ phase : Phase p.n, window model S 1 K (GeneralPaperOriginalGameInput.equalInput model p) phase ≤
      profile model S K (GeneralPaperOriginalGameInput.equalInput model p) := by
  dsimp only
  intro phase
  apply all_phases
  rw [GeneralPaperOriginalMeasuredReference.word]
  exact Nat.mul_le_mul hK (GeneralPaperEqualInputDomain.logarithm_positive
    (GeneralPaperOriginalGameInput.equalInput model p))

end Blotto.GeneralPaperMixedInitializerPhases
