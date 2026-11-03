import Blotto.GeneralPaperCompleteParsedPreparationWork

/-! The successful frame parser's accuracy-selection work cancels exactly
against the pass omitted by parsed continuation. The remaining two reads,
control and final attachment have uniform input-size prices. No parser
capacity premise or second accuracy preparation is needed. -/
namespace Blotto.GeneralPaperCompleteFramedPreparationWork
open GeneralPaperBinaryAccuracy (Parsed)
open GeneralPaperStoredParsedPreparation (input prepare width)
open GeneralPaperEqualInputDomain
open GeneralPaperUniformResourceGrowth GeneralPaperEqualUniformRateAlgebra
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

theorem parser_remainder (A : ℕ) (frame suffix : List Bool) (parsed : Parsed)
    (hRead : (GeneralPaperBinaryAccuracy.read id A frame).1 = some (parsed,suffix)) :
    (GeneralPaperBinaryAccuracy.read id A frame).2 ≤
      4 * (frame.length + 1) * A + (GeneralPaperBinaryAccuracy.prepare id A parsed.words).2 + 64 * A := by
  have hFirst := BinaryPositiveWordReadWork.read_bound frame
  unfold GeneralPaperBinaryAccuracy.read at hRead ⊢
  dsimp only at hRead ⊢
  cases hn : (BinaryPositiveWordReadWork.read frame).1 with
  | none => simp only [hn] at hRead; cases hRead
  | some numerator =>
    simp only [hn] at hRead ⊢
    have hSecond := BinaryPositiveWordReadWork.read_bound numerator.2
    have hLength := BinaryPositiveWordReadWork.read_suffix_length frame numerator hn
    cases hd : (BinaryPositiveWordReadWork.read numerator.2).1 with
    | none => simp only [hd] at hRead; cases hRead
    | some denominator =>
      simp only [hd] at hRead ⊢
      have hWords := congrArg (fun pair : Parsed × List Bool => pair.1.words) (Option.some.inj hRead)
      dsimp only at hWords
      rw [← hWords]
      have hReads := Nat.mul_le_mul_right A
        (show (BinaryPositiveWordReadWork.read frame).2 +
          (BinaryPositiveWordReadWork.read numerator.2).2 ≤ 4 * (frame.length + 1) by omega)
      omega

def price (model : RationalCostModel) (K : ℕ) (p : Input model) : ℕ :=
  GeneralPaperCompleteStoredPipelineWork.price model K p +
    4 * (2 * (accuracySize p + 1) + 1) * word K p + 64 * word K p +
    64 * (word K p + (GeneralPaperEqualCopiedPipeline.run model (word K p) K p).1.address + 1)

theorem work {n : ℕ} (model : RationalCostModel) (K : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n)
    (hv : ∀ j,values.read j = v.weight j) (budget : ℚ) (parsed : Parsed) (frame suffix : List Bool)
    (hRead : (GeneralPaperBinaryAccuracy.read id (word K (input model values v hv budget parsed)) frame).1 = some (parsed,suffix))
    (hLength : frame.length ≤ 2 * (accuracySize (input model values v hv budget parsed) + 1)) :
    (GeneralPaperStoredFramedPreparation.run model (word K (input model values v hv budget parsed))
      K values v hv budget frame).2 ≤ price model K (input model values v hv budget parsed) := by
  have hFrame := GeneralPaperStoredFramedWork.frame_work model _ K values v hv budget frame suffix parsed hRead
  have hParser := parser_remainder _ frame suffix parsed hRead
  have hJoin := GeneralPaperCompleteParsedPreparationWork.work_identity model
    (word K (input model values v hv budget parsed)) K values v hv budget parsed
  have hFull := GeneralPaperCompleteStoredPipelineWork.work model K (input model values v hv budget parsed)
  have hWidth := congrArg (fun a => a.address)
    (GeneralPaperStoredParsedPreparation.prepared_data model
      (word K (input model values v hv budget parsed)) K values v hv budget parsed)
  have hReads := Nat.mul_le_mul_right (word K (input model values v hv budget parsed))
    (Nat.mul_le_mul_left 4 (Nat.add_le_add_right hLength 1))
  change width model (word K (input model values v hv budget parsed)) K values v hv budget parsed = _ at hWidth
  unfold price
  omega

theorem returned_work {n : ℕ} (model : RationalCostModel) (K : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n)
    (hv : ∀ j,values.read j = v.weight j) (budget : ℚ) (parsed : Parsed) (frame suffix : List Bool)
    (hRead : (GeneralPaperBinaryAccuracy.read id (word K (input model values v hv budget parsed)) frame).1 = some (parsed,suffix))
    (hLength : frame.length ≤ 2 * (accuracySize (input model values v hv budget parsed) + 1))
    (returned : GeneralPaperStoredFramedPreparation.Output)
    (hReturn : (GeneralPaperStoredFramedPreparation.run model (word K (input model values v hv budget parsed))
      K values v hv budget frame).1 = some returned) :
    returned.2.1.work ≤ price model K (input model values v hv budget parsed) := by
  obtain ⟨_,_,_,_,_,_,hWork⟩ := GeneralPaperStoredFramedPreparation.every_returned model _ K values v hv budget frame returned hReturn
  rw [hWork]
  exact work model K values v hv budget parsed frame suffix hRead hLength

theorem price_rate (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) (K : ℕ) :
    Bound (price model K) ledger logarithm := by
  have hL : ∀ p : Input model,1 ≤ logarithm p := logarithm_positive
  have hr : ∀ p : Input model,1 ≤ ledger p := ledger_positive
  have hOld := GeneralPaperCompleteStoredPipelineWork.price_rate model hFast K
  have hAcc : Bound (accuracySize (model := model)) ledger logarithm := by
    refine ⟨1,0,fun p => ?_⟩
    simp only [pow_zero,Nat.one_mul,Nat.mul_one]
    unfold ledger
    omega
  have hSP := polylog_of_tight (word_tight K model)
  have hAP : Polylog (fun p : Input model => (GeneralPaperEqualCopiedPipeline.run model (word K p) K p).1.address) logarithm :=
    polylog_of_tight (GeneralPaperSelectedPreparationInputRates.address_tight model K (word K))
  unfold price
  fun_prop

theorem canonical_length {n : ℕ} (model : RationalCostModel) (A : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n)
    (hv : ∀ j,values.read j = v.weight j) (budget eps : ℚ) (hPositive : 0 < eps) (parsed : Parsed)
    (hRead : (GeneralPaperBinaryAccuracy.read id A
      (BinaryAccuracyFrame.encode (GeneralPaperBinaryAccuracy.input eps hPositive))).1 = some (parsed,[])) :
    (BinaryAccuracyFrame.encode (GeneralPaperBinaryAccuracy.input eps hPositive)).length =
      2 * (accuracySize (input model values v hv budget parsed) + 1) := by
  obtain ⟨other,hOther,hNumeric⟩ := GeneralPaperBinaryAccuracy.read_complete id A
    (GeneralPaperBinaryAccuracy.input eps hPositive) []
  simp only [List.append_nil] at hOther
  have hEq : other = parsed := congrArg Prod.fst (Option.some.inj (hOther.symm.trans hRead))
  rw [hEq] at hNumeric
  have hSize := GeneralPaperBinaryAccuracyConstructionStorage.rational_input_size eps hPositive parsed.words hNumeric
  rw [GeneralPaperBinaryAccuracy.input_length]
  change 2 * rationalWordWidth eps = 2 * (GeneralPaperBinaryAccuracyConstructionStorage.inputSize parsed.words + 1)
  rw [hSize]

theorem paper_time (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) (K : ℕ) :
    ∃ C d : ℕ,∀ (n : ℕ) (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n)
      (hv : ∀ j,values.read j = v.weight j) (budget eps : ℚ) (hPositive : 0 < eps) (parsed : Parsed),
      let p := input model values v hv budget parsed
      let frame := BinaryAccuracyFrame.encode (GeneralPaperBinaryAccuracy.input eps hPositive)
      (GeneralPaperBinaryAccuracy.read id (word K p) frame).1 = some (parsed,[]) →
      (GeneralPaperStoredFramedPreparation.run model (word K p) K values v hv budget frame).2 ≤
        C * GeneralPaperEqualInputHeadline.inputSize p * (GeneralPaperEqualInputHeadline.paperLog p) ^ d := by
  obtain ⟨C,d,hPrice⟩ := GeneralPaperEqualInputHeadline.transfer_rate (price_rate model hFast K)
  refine ⟨C,d,fun _ values v hv budget eps hPositive parsed hRead => ?_⟩
  exact (work model K values v hv budget parsed _ [] hRead
    (canonical_length model _ values v hv budget eps hPositive parsed hRead).le).trans (hPrice _)

theorem parser_data_width (A B : ℕ) (frame : List Bool) :
    (GeneralPaperBinaryAccuracy.read id A frame).1 = (GeneralPaperBinaryAccuracy.read id B frame).1 := by
  unfold GeneralPaperBinaryAccuracy.read
  dsimp only
  cases (BinaryPositiveWordReadWork.read frame).1 with
  | none => simp only
  | some numerator =>
    simp only
    cases (BinaryPositiveWordReadWork.read numerator.2).1 with
    | none => simp only
    | some denominator =>
      simp only [GeneralPaperBinaryAccuracy.prepare_data]

theorem epsilon_constructed {n : ℕ} (model : RationalCostModel) (K : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n)
    (hv : ∀ j,values.read j = v.weight j) (budget : ℚ) (hBudget : 0 < budget)
    (eps : ℚ) (hPositive : 0 < eps) (hOne : eps < 1) :
    ∃ (parsed : Parsed) (returned : GeneralPaperStoredFramedPreparation.Output),
      let p := input model values v hv budget parsed
      let A := word K p
      let frame := BinaryAccuracyFrame.encode (GeneralPaperBinaryAccuracy.input eps hPositive)
      (GeneralPaperBinaryAccuracy.read id A frame).1 = some (parsed,[]) ∧
      GeneralPaperStoredFramedContract.epsilon parsed = eps ∧
      parsed.exponent = (GeneralPaperDyadicAccuracy.prepare eps).exponent ∧
      (GeneralPaperStoredFramedPreparation.run model A K values v hv budget frame).1 = some returned ∧
      returned.2.2 = [] ∧
      returned.2.1.work = (GeneralPaperStoredFramedPreparation.run model A K values v hv budget frame).2 ∧
      returned.2.1.work ≤ price model K p ∧
      let μ := GeneralPaperStoredSelectedLaw.outputLaw model returned.1 returned.2.1
        (prepare model A K values v hv budget parsed).1.branch
      Supported (budget : ℝ) μ ∧ regret v.values (budget : ℝ) μ μ ≤ (eps : ℝ) := by
  obtain ⟨parsed,hRead,_⟩ := GeneralPaperBinaryAccuracy.read_complete id 1
    (GeneralPaperBinaryAccuracy.input eps hPositive) []
  simp only [List.append_nil] at hRead
  let A := word K (input model values v hv budget parsed)
  have hCalibrated : (GeneralPaperBinaryAccuracy.read id A
      (BinaryAccuracyFrame.encode (GeneralPaperBinaryAccuracy.input eps hPositive))).1 = some (parsed,[]) :=
    (parser_data_width A 1 _).trans hRead
  obtain ⟨other,returned,hOther,hEps,hExponent,hReturn,hSuffix,hWork,_,hLaw⟩ :=
    GeneralPaperStoredCanonicalFrame.epsilon_constructed model A K values v hv budget hBudget eps hPositive hOne []
  simp only [List.append_nil] at hOther hReturn hWork
  have hEq : other = parsed := congrArg Prod.fst (Option.some.inj (hOther.symm.trans hCalibrated))
  subst other
  refine ⟨parsed,returned,hCalibrated,hEps,hExponent,hReturn,hSuffix,hWork,?_,hLaw⟩
  exact returned_work model K values v hv budget parsed _ [] hCalibrated
    (canonical_length model A values v hv budget eps hPositive parsed hCalibrated).le returned hReturn

end Blotto.GeneralPaperCompleteFramedPreparationWork
