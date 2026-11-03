import Blotto.GeneralPaperEqualInputInitialization

/-! Generalization of the checked initializer observer to inputs before
branch selection. No proof below uses a small-field premise. All original
owners, every sizing cursor/frame, scalar/control and return stay counted.
The final bridges identify the previous grouped observers exactly. -/
namespace Blotto.GeneralPaperEqualInputInitializerLifetime
open GeneralPaperEqualInputDomain
open GeneralPaperEncodedScalarStorage (natBits fields)
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

def valueWords (model : RationalCostModel) (W : ℕ) (p : Input model) := GeneralPaperValueInputWordLength.run model W p.values

def budgetWords (model : RationalCostModel) (W : ℕ) (p : Input model) := GeneralPaperStoredRationalWordLength.run model W p.budget

def numeratorWords (model : RationalCostModel) (W : ℕ) (p : Input model) := GeneralPaperBinaryAccuracy.count id W p.words.numerator.bits

def denominatorWords (model : RationalCostModel) (W : ℕ) (p : Input model) := GeneralPaperBinaryAccuracy.count id W p.words.denominator.bits

def accuracySum (model : RationalCostModel) (W : ℕ) (p : Input model) := GeneralPaperNaturalScalarStep.run model W .add (numeratorWords model W p).1 (denominatorWords model W p).1

def builtReference (model : RationalCostModel) (W K : ℕ) (p : Input model) :=
  GeneralPaperEqualReferenceConstruction.run model W K p.n p.k (valueWords model W p).1 (budgetWords model W p).1 (accuracySum model W p).1

theorem value_data (model : RationalCostModel) (W : ℕ) (p : Input model) : (valueWords model W p).1 = originalSize p :=
  GeneralPaperValueInputWordLength.data model W p.values

theorem budget_data (model : RationalCostModel) (W : ℕ) (p : Input model) : (budgetWords model W p).1 = budgetSize p :=
  GeneralPaperStoredRationalWordLength.data model W p.budget

theorem numerator_data (model : RationalCostModel) (W : ℕ) (p : Input model) : (numeratorWords model W p).1 = p.words.numerator.width := by
  simp only [numeratorWords, GeneralPaperBinaryAccuracy.count_data, PositiveBinaryWord.bits, PositiveBinaryWord.width, List.length_cons]

theorem denominator_data (model : RationalCostModel) (W : ℕ) (p : Input model) : (denominatorWords model W p).1 = p.words.denominator.width := by
  simp only [denominatorWords, GeneralPaperBinaryAccuracy.count_data, PositiveBinaryWord.bits, PositiveBinaryWord.width, List.length_cons]

theorem accuracy_data (model : RationalCostModel) (W : ℕ) (p : Input model) : (accuracySum model W p).1 = accuracySize p := by
  simp only [accuracySum, numerator_data, denominator_data, GeneralPaperNaturalScalarStep.data, GeneralPaperNaturalScalarStep.Op.apply,
    accuracySize, GeneralPaperBinaryAccuracyConstructionStorage.inputSize]
  omega

theorem built_data (model : RationalCostModel) (W K : ℕ) (p : Input model) :
    (builtReference model W K p).1 = GeneralPaperEqualInputDomain.word K p :=
  GeneralPaperEqualInputInitialization.measured_word_eq model W K p

theorem price_shape (model : RationalCostModel) (W K : ℕ) (p : Input model) :
    (GeneralPaperEqualInputInitialization.prepareReference model W K p).2 =
      (GeneralPaperBinaryAccuracy.prepare id W p.words).2 +
      ((valueWords model W p).2 + (budgetWords model W p).2 + (numeratorWords model W p).2 +
        (denominatorWords model W p).2 + (accuracySum model W p).2 + (builtReference model W K p).2 + 128 * W + 128) + 64 * W + 64 := by
  have hk := GeneralPaperEqualInputInitialization.initialized_exponent model W K p
  change (GeneralPaperBinaryAccuracy.prepare id W p.words).1 = p.k at hk
  unfold GeneralPaperEqualInputInitialization.prepareReference
  change (GeneralPaperBinaryAccuracy.prepare id W p.words).2 +
    (GeneralPaperEqualReferenceConstruction.measured model W K
      (GeneralPaperBinaryAccuracy.prepare id W p.words).1 p.values p.budget p.words).2 + 64 * W + 64 = _
  rw [hk]
  rfl

def inputOwner (model : RationalCostModel) (W : ℕ) (p : Input model) : ℕ :=
  GeneralPaperEncodedBasisStorage.arrayFootprint W rationalWordWidth p.values + rationalWordWidth p.budget +
    GeneralPaperBooleanRulerWorkStorage.wordFoot W p.words.numerator +
    GeneralPaperBooleanRulerWorkStorage.wordFoot W p.words.denominator + 64 * W

def inputProfile (model : RationalCostModel) (W : ℕ) (p : Input model) : ℕ :=
  originalSize p + p.n * W + budgetSize p + accuracySize p * (1 + 2 * W) + 320 * W

theorem input_bound (model : RationalCostModel) (W : ℕ) (p : Input model) : inputOwner model W p ≤ inputProfile model W p := by
  have hn := GeneralPaperBooleanRulerWorkStorage.word_bound W p.words.numerator
  have hd := GeneralPaperBooleanRulerWorkStorage.word_bound W p.words.denominator
  unfold inputOwner inputProfile
  rw [GeneralPaperEqualPrefixOwners.original_exact]
  dsimp only [originalSize, budgetSize, accuracySize, GeneralPaperBinaryAccuracyConstructionStorage.inputSize]
  nlinarith only [hn, hd]

def controlCap (model : RationalCostModel) (W K : ℕ) (p : Input model) : ℕ :=
  p.n + p.k + W + K + originalSize p + budgetSize p + accuracySize p + GeneralPaperEqualInputDomain.word K p +
    GeneralPaperEqualInputInitialization.initializationPrice model W K p + 1

def controls (model : RationalCostModel) (W K : ℕ) (p : Input model) : ℕ :=
  let v := valueWords model W p
  let b := budgetWords model W p
  let num := numeratorWords model W p
  let den := denominatorWords model W p
  let e := accuracySum model W p
  let built := builtReference model W K p
  let prec := GeneralPaperBinaryAccuracy.prepare id W p.words
  let actual := GeneralPaperEqualInputInitialization.prepareReference model W K p
  fields W [p.n, p.k, W, K, v.1, b.1, num.1, den.1, e.1, built.1, prec.2, v.2, b.2, num.2, den.2, e.2, built.2, actual.2, v.2+b.2, v.2+b.2+num.2, v.2+b.2+num.2+den.2, v.2+b.2+num.2+den.2+e.2, v.2+b.2+num.2+den.2+e.2+built.2, v.2+b.2+num.2+den.2+e.2+built.2+128*W+128, prec.2+(v.2+b.2+num.2+den.2+e.2+built.2+128*W+128), 64*W, 64, 128*W, 128] + 256 * W

def controlProfile (model : RationalCostModel) (W K : ℕ) (p : Input model) : ℕ :=
  29 * (natBits (controlCap model W K p) + W) + 288 * W

theorem controls_bound (model : RationalCostModel) (W K : ℕ) (p : Input model) : controls model W K p ≤ controlProfile model W K p := by
  have hF := GeneralPaperEqualInputInitialization.initialization_work model W K p
  have hShape := price_shape model W K p
  have hk := GeneralPaperEqualInputInitialization.initialized_exponent model W K p
  have hNum : p.words.numerator.width ≤ accuracySize p := by unfold accuracySize GeneralPaperBinaryAccuracyConstructionStorage.inputSize; omega
  have hDen : p.words.denominator.width ≤ accuracySize p := by unfold accuracySize GeneralPaperBinaryAccuracyConstructionStorage.inputSize; omega
  unfold controls
  dsimp only
  have h := GeneralPaperExpressionArrayReturns.fields_mono_cap W (controlCap model W K p)
    [p.n, p.k, W, K, (valueWords model W p).1, (budgetWords model W p).1, (numeratorWords model W p).1, (denominatorWords model W p).1, (accuracySum model W p).1, (builtReference model W K p).1, (GeneralPaperBinaryAccuracy.prepare id W p.words).2, (valueWords model W p).2, (budgetWords model W p).2, (numeratorWords model W p).2, (denominatorWords model W p).2, (accuracySum model W p).2, (builtReference model W K p).2, (GeneralPaperEqualInputInitialization.prepareReference model W K p).2, (valueWords model W p).2+(budgetWords model W p).2, (valueWords model W p).2+(budgetWords model W p).2+(numeratorWords model W p).2, (valueWords model W p).2+(budgetWords model W p).2+(numeratorWords model W p).2+(denominatorWords model W p).2, (valueWords model W p).2+(budgetWords model W p).2+(numeratorWords model W p).2+(denominatorWords model W p).2+(accuracySum model W p).2, (valueWords model W p).2+(budgetWords model W p).2+(numeratorWords model W p).2+(denominatorWords model W p).2+(accuracySum model W p).2+(builtReference model W K p).2, (valueWords model W p).2+(budgetWords model W p).2+(numeratorWords model W p).2+(denominatorWords model W p).2+(accuracySum model W p).2+(builtReference model W K p).2+128*W+128, (GeneralPaperBinaryAccuracy.prepare id W p.words).2+((valueWords model W p).2+(budgetWords model W p).2+(numeratorWords model W p).2+(denominatorWords model W p).2+(accuracySum model W p).2+(builtReference model W K p).2+128*W+128), 64*W, 64, 128*W, 128] (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      simp only [value_data, budget_data, numerator_data, denominator_data, accuracy_data, built_data] at hx
      unfold controlCap
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
  change fields W _ ≤ 29 * (natBits (controlCap model W K p) + W) + 32 * W at h
  unfold controlProfile
  omega


inductive Phase (n : ℕ) where
  | accuracy
  | indices (cursor : ℕ) (h : cursor ≤ n)
  | values (cursor : ℕ) (h : cursor ≤ n)
  | budget
  | numerator
  | denominator
  | sum
  | word
  | returned

def cursorControls (W : ℕ) {n : ℕ} : Phase n → ℕ
  | .indices cursor _ => fields W [cursor]
  | .values cursor _ => fields W [cursor]
  | _ => 0

def cursorProfile (W n : ℕ) : ℕ := natBits (n + 1) + 33 * W

theorem cursor_bound (W n : ℕ) (phase : Phase n) : cursorControls W phase ≤ cursorProfile W n := by
  have hCursor (cursor : ℕ) (hc : cursor ≤ n) : fields W [cursor] ≤ cursorProfile W n := by
    have h := GeneralPaperExpressionArrayReturns.fields_mono_cap W (n + 1) [cursor] (by
      intro x hx
      rw [List.mem_singleton.mp hx]
      omega)
    simp only [List.length_singleton, Nat.one_mul] at h
    change fields W [cursor] ≤ natBits (n + 1) + W + 32 * W at h
    unfold cursorProfile
    omega
  cases phase <;> simp only [cursorControls]
  all_goals first | exact hCursor _ (by assumption) | exact Nat.zero_le _

def returnedOwner (model : RationalCostModel) (W K : ℕ) (p : Input model) : ℕ :=
  let actual := GeneralPaperEqualInputInitialization.prepareReference model W K p
  fields W [actual.1.1, actual.1.2, actual.2] + 64 * W

def returnedProfile (model : RationalCostModel) (W K : ℕ) (p : Input model) : ℕ :=
  3 * (natBits (controlCap model W K p) + W) + 96 * W

theorem returned_bound (model : RationalCostModel) (W K : ℕ) (p : Input model) :
    returnedOwner model W K p ≤ returnedProfile model W K p := by
  have hk := GeneralPaperEqualInputInitialization.initialized_exponent model W K p
  have hw := GeneralPaperEqualInputInitialization.initialized_word model W K p
  have hF := GeneralPaperEqualInputInitialization.initialization_work model W K p
  have h := GeneralPaperExpressionArrayReturns.fields_mono_cap W (controlCap model W K p)
    [(GeneralPaperEqualInputInitialization.prepareReference model W K p).1.1,
      (GeneralPaperEqualInputInitialization.prepareReference model W K p).1.2,
      (GeneralPaperEqualInputInitialization.prepareReference model W K p).2] (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · rw [hk]; unfold controlCap; omega
      · rw [hw]; unfold controlCap; omega
      · unfold controlCap; omega)
  change fields W _ ≤ 3 * (natBits (controlCap model W K p) + W) + 32 * W at h
  simp only [returnedOwner, returnedProfile]
  omega

def sumProfile (model : RationalCostModel) (W E : ℕ) : ℕ :=
  32 * (5 * model.rat (1 + binaryWordWidth E) + 16 * W + 16)

theorem sum_bound (model : RationalCostModel) (W : ℕ) (p : Input model) :
    GeneralPaperNaturalScalarLifetime.footprint model W .add (numeratorWords model W p).1 (denominatorWords model W p).1 ≤
      sumProfile model W (accuracySize p) := by
  have hNum : p.words.numerator.width ≤ accuracySize p := by unfold accuracySize GeneralPaperBinaryAccuracyConstructionStorage.inputSize; omega
  have hDen : p.words.denominator.width ≤ accuracySize p := by unfold accuracySize GeneralPaperBinaryAccuracyConstructionStorage.inputSize; omega
  have hSum : p.words.numerator.width + p.words.denominator.width = accuracySize p := by
    unfold accuracySize GeneralPaperBinaryAccuracyConstructionStorage.inputSize
    omega
  have hn := binaryWordWidth_mono hNum
  have hd := binaryWordWidth_mono hDen
  have hWork := GeneralPaperNaturalScalarStep.work model W .add p.words.numerator.width p.words.denominator.width
    (1 + binaryWordWidth (accuracySize p))
    (by unfold GeneralPaperNaturalScalarStep.word; omega)
    (by unfold GeneralPaperNaturalScalarStep.word; omega)
    (by change 1 + binaryWordWidth (p.words.numerator.width + p.words.denominator.width) ≤ _; rw [hSum])
  simp only [numerator_data, denominator_data]
  exact (GeneralPaperNaturalScalarLifetime.bounded model W .add _ _).trans (Nat.mul_le_mul_left 32 hWork)

def component (model : RationalCostModel) (W K : ℕ) (p : Input model) : Phase p.n → ℕ
  | .accuracy => GeneralPaperBinaryAccuracyConstructionStorage.window W p.words
  | .indices cursor _ => GeneralPaperPackingAllocationLifetime.indicesLive W p.n cursor
  | .values _ _ => GeneralPaperValueInputLengthLifetime.window model W p.values 0
  | .budget => GeneralPaperWordLengthLifetime.rationalFoot model W p.budget
  | .numerator => GeneralPaperAccuracyCountConstructionStorage.window W p.words.numerator.bits
  | .denominator => GeneralPaperAccuracyCountConstructionStorage.window W p.words.denominator.bits
  | .sum => GeneralPaperNaturalScalarLifetime.footprint model W .add (numeratorWords model W p).1 (denominatorWords model W p).1
  | .word => GeneralPaperEqualReferenceWordLifetime.footprint model W K p.n p.k
      (valueWords model W p).1 (budgetWords model W p).1 (accuracySum model W p).1
  | .returned => returnedOwner model W K p

def scratchProfile (model : RationalCostModel) (W K : ℕ) (p : Input model) : ℕ :=
  GeneralPaperBinaryAccuracyConstructionStorage.profile W (accuracySize p) +
    GeneralPaperPackingAllocationLifetime.indicesProfile W p.n +
    GeneralPaperValueInputLengthLifetime.profile model W p.n (originalSize p) 0 +
    GeneralPaperWordLengthLifetime.rationalProfile model W (budgetSize p) +
    GeneralPaperAccuracyCountConstructionStorage.profile W (accuracySize p) +
    sumProfile model W (accuracySize p) +
    GeneralPaperEqualReferenceWordLifetime.profile model W K p.n p.k (originalSize p) (budgetSize p) (accuracySize p) +
    returnedProfile model W K p

theorem component_bound (model : RationalCostModel) (W K : ℕ) (p : Input model) (phase : Phase p.n) :
    component model W K p phase ≤ scratchProfile model W K p := by
  have hAccuracy := GeneralPaperBinaryAccuracyConstructionStorage.bounded W p.words
  change GeneralPaperBinaryAccuracyConstructionStorage.window W p.words ≤
    GeneralPaperBinaryAccuracyConstructionStorage.profile W (accuracySize p) at hAccuracy
  have hIndices := GeneralPaperPackingAllocationLifetime.indices_bound W p.n
  have hValues := GeneralPaperValueInputLengthLifetime.bounded model W p.values 0
  have hBudget := GeneralPaperWordLengthLifetime.rational_input_bound model W p.budget
  change GeneralPaperValueInputLengthLifetime.window model W p.values 0 ≤
    GeneralPaperValueInputLengthLifetime.profile model W p.n (originalSize p) 0 at hValues
  change GeneralPaperWordLengthLifetime.rationalFoot model W p.budget ≤
    GeneralPaperWordLengthLifetime.rationalProfile model W (budgetSize p) at hBudget
  have hNum := GeneralPaperAccuracyCountConstructionStorage.bounded W (accuracySize p) p.words.numerator.bits (by
    simp only [PositiveBinaryWord.bits, List.length_cons]
    unfold accuracySize GeneralPaperBinaryAccuracyConstructionStorage.inputSize PositiveBinaryWord.width
    omega)
  have hDen := GeneralPaperAccuracyCountConstructionStorage.bounded W (accuracySize p) p.words.denominator.bits (by
    simp only [PositiveBinaryWord.bits, List.length_cons]
    unfold accuracySize GeneralPaperBinaryAccuracyConstructionStorage.inputSize PositiveBinaryWord.width
    omega)
  have hSum := sum_bound model W p
  have hWord := GeneralPaperEqualReferenceWordLifetime.source_bound model W K p.n p.k
    (valueWords model W p).1 (budgetWords model W p).1 (accuracySum model W p).1
  simp only [value_data, budget_data, accuracy_data] at hWord
  have hReturn := returned_bound model W K p
  cases phase with
  | indices cursor hc =>
    have h := hIndices cursor hc
    simp only [component]
    unfold scratchProfile
    omega
  | word =>
    simp only [component, value_data, budget_data, accuracy_data]
    unfold scratchProfile
    omega
  | _ =>
    simp only [component]
    unfold scratchProfile
    all_goals omega

def window (model : RationalCostModel) (W K : ℕ) (p : Input model) (phase : Phase p.n) : ℕ :=
  inputOwner model W p + controls model W K p + cursorControls W phase + component model W K p phase

def profile (model : RationalCostModel) (W K : ℕ) (p : Input model) : ℕ :=
  inputProfile model W p + controlProfile model W K p + cursorProfile W p.n + scratchProfile model W K p

theorem all_phases (model : RationalCostModel) (W K : ℕ) (p : Input model) (phase : Phase p.n) :
    window model W K p phase ≤ profile model W K p :=
  Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (input_bound model W p) (controls_bound model W K p))
    (cursor_bound W p.n phase)) (component_bound model W K p phase)

theorem grouped_profile (model : RationalCostModel) (W K : ℕ) (p : Input model)
    (small : ∀ j, 2 * (GeneralPaperEqualNativeSampler.rounded true model 1 p.k p.values p.selector p.correct).weight j ≤ 1) :
    profile model W K p = GeneralPaperEqualInitializerLifetime.profile model W K (grouped p small) := rfl

def groupedPhase {n : ℕ} : GeneralPaperEqualInitializerLifetime.Phase n → Phase n
  | .accuracy => .accuracy
  | .indices c h => .indices c h
  | .values c h => .values c h
  | .budget => .budget
  | .numerator => .numerator
  | .denominator => .denominator
  | .sum => .sum
  | .word => .word
  | .returned => .returned

theorem grouped_window (model : RationalCostModel) (W K : ℕ) (p : Input model)
    (small : ∀ j, 2 * (GeneralPaperEqualNativeSampler.rounded true model 1 p.k p.values p.selector p.correct).weight j ≤ 1)
    (phase : GeneralPaperEqualInitializerLifetime.Phase p.n) :
    window model W K p (groupedPhase phase) =
      GeneralPaperEqualInitializerLifetime.window model W K (grouped p small) phase := by
  cases phase <;> rfl

end Blotto.GeneralPaperEqualInputInitializerLifetime
