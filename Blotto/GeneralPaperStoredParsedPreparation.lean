import Blotto.GeneralPaperStoredSelectedOutput

/-! Continue from the actual accuracy parser's exponent. One measured
reference, dispatch/close/copy and stored construction follow; accuracy is
not read or prepared again. Equality transports are erased. -/
namespace Blotto.GeneralPaperStoredParsedPreparation
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperBinaryAccuracy (Parsed)
open GeneralPaperEqualInputDomain (Input word)
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 8192

def input {n : ℕ} (model : RationalCostModel) (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n)
    (hv : ∀ j,values.read j = v.weight j) (budget : ℚ) (parsed : Parsed) : Input model :=
  ⟨n,values,v,hv,parsed.exponent,parsed.words,
    parsed.correct.trans (GeneralPaperBinaryAccuracy.prepare_data id 1 parsed.words).symm,budget⟩

theorem reference_data {n : ℕ} (model : RationalCostModel) (A K : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j)
    (budget : ℚ) (parsed : Parsed) :
    (GeneralPaperEqualReferenceConstruction.measured model A K parsed.exponent values budget parsed.words).1 =
      word K (input model values v hv budget parsed) :=
  GeneralPaperEqualInputInitialization.measured_word_eq model A K (input model values v hv budget parsed)

def prepare {n : ℕ} (model : RationalCostModel) (A K : ℕ) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j) (budget : ℚ) (parsed : Parsed) :=
  let reference := GeneralPaperEqualReferenceConstruction.measured model A K parsed.exponent values budget parsed.words
  let actual := GeneralPaperEqualCopiedPipeline.dispatchCloseCopy model reference.1 parsed.exponent values v hv budget
  let source := GeneralPaperEqualSelectedPipeline.transport model reference.1 parsed.exponent
    (word K (input model values v hv budget parsed)) parsed.exponent values v hv budget
    (reference_data model A K values v hv budget parsed) rfl actual.1
  (source,reference.2 + actual.2 + 64 * (A + 1))

theorem prepared_data {n : ℕ} (model : RationalCostModel) (A K : ℕ) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j) (budget : ℚ) (parsed : Parsed) :
    (prepare model A K values v hv budget parsed).1 =
      (GeneralPaperEqualCopiedPipeline.run model A K (input model values v hv budget parsed)).1 := by
  rw [GeneralPaperEqualCopiedPipeline.data]
  exact GeneralPaperEqualCopiedPipeline.transport_data model _ _ _ _ values v hv budget
    (reference_data model A K values v hv budget parsed) rfl

theorem prepared_work {n : ℕ} (model : RationalCostModel) (A K : ℕ) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j) (budget : ℚ) (parsed : Parsed) :
    (prepare model A K values v hv budget parsed).2 =
      (GeneralPaperEqualReferenceConstruction.measured model A K parsed.exponent values budget parsed.words).2 +
      (GeneralPaperEqualCopiedPipeline.dispatchCloseCopy model
        (word K (input model values v hv budget parsed)) parsed.exponent values v hv budget).2 + 64 * (A + 1) := by
  have h := GeneralPaperEqualCopiedPipeline.price_congr model
    (GeneralPaperEqualReferenceConstruction.measured model A K parsed.exponent values budget parsed.words).1 parsed.exponent
    (word K (input model values v hv budget parsed)) parsed.exponent values v hv budget
    (reference_data model A K values v hv budget parsed) rfl
  exact congrArg (fun w => (GeneralPaperEqualReferenceConstruction.measured model A K parsed.exponent values budget parsed.words).2 + w + 64 * (A + 1)) h

def width {n : ℕ} (model : RationalCostModel) (A K : ℕ) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j) (budget : ℚ) (parsed : Parsed) :=
  (prepare model A K values v hv budget parsed).1.address

def run {n : ℕ} (model : RationalCostModel) (A K : ℕ) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j) (budget : ℚ) (parsed : Parsed) :
    Option (Installed (width model A K values v hv budget parsed)) × ℕ :=
  let prepared := prepare model A K values v hv budget parsed
  let W := word K (input model values v hv budget parsed)
  let actual := GeneralPaperStoredSelectedConstruction.run model W prepared.1
  match actual.1 with
  | none => (none,prepared.2 + actual.2 + 64 * (W + prepared.1.address + 1))
  | some output =>
    let finished := GeneralPaperSamplerRecordInstallation.attach W prepared.1.address prepared.2 output
    (some finished,finished.work)

theorem source {n : ℕ} (model : RationalCostModel) (A K : ℕ) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j) (budget : ℚ) (parsed : Parsed) :
    ∃ returned : Installed (width model A K values v hv budget parsed),
      (run model A K values v hv budget parsed).1 = some returned ∧
      returned.work = (run model A K values v hv budget parsed).2 ∧
      GeneralPaperStoredSelectedDraw.Refines model (width model A K values v hv budget parsed) returned
        (prepare model A K values v hv budget parsed).1.branch := by
  let prepared := prepare model A K values v hv budget parsed
  let W := word K (input model values v hv budget parsed)
  obtain ⟨inner,hBuilt,_,_⟩ := GeneralPaperStoredSelectedConstruction.source model W W parsed.exponent values v hv budget prepared.1
  have hRefines := GeneralPaperStoredSelectedDraw.every_returned model W W parsed.exponent values v hv budget prepared.1 inner hBuilt
  let output := GeneralPaperSamplerRecordInstallation.attach W prepared.1.address prepared.2 inner
  refine ⟨output,?_,?_,GeneralPaperStoredSelectedExt.attach model W prepared.1.address prepared.2 inner prepared.1.branch hRefines⟩
  · simp only [run,prepared,W,hBuilt,output]
  · simp only [run,prepared,W,hBuilt,output]

theorem every_returned {n : ℕ} (model : RationalCostModel) (A K : ℕ) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j) (budget : ℚ) (parsed : Parsed)
    (returned : Installed (width model A K values v hv budget parsed))
    (hReturn : (run model A K values v hv budget parsed).1 = some returned) :
    returned.work = (run model A K values v hv budget parsed).2 ∧
      GeneralPaperStoredSelectedDraw.Refines model (width model A K values v hv budget parsed) returned
        (prepare model A K values v hv budget parsed).1.branch := by
  obtain ⟨actual,hActual,hWork,hRefines⟩ := source model A K values v hv budget parsed
  have hEq : actual = returned := Option.some.inj (hActual.symm.trans hReturn)
  rw [← hEq]
  exact ⟨hWork,hRefines⟩

theorem epsilon {n : ℕ} (model : RationalCostModel) (A K : ℕ) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j) (budget : ℚ) (hBudget : 0 < budget) (parsed : Parsed)
    (hOne : GeneralPaperEqualInputHeadline.epsilon (input model values v hv budget parsed) < 1)
    (returned : Installed (width model A K values v hv budget parsed))
    (hReturn : (run model A K values v hv budget parsed).1 = some returned) :
    let μ := GeneralPaperStoredSelectedLaw.outputLaw model (width model A K values v hv budget parsed) returned
      (prepare model A K values v hv budget parsed).1.branch
    Supported (budget : ℝ) μ ∧ regret v.values (budget : ℝ) μ μ ≤
      (GeneralPaperEqualInputHeadline.epsilon (input model values v hv budget parsed) : ℝ) := by
  dsimp only
  rw [GeneralPaperStoredSelectedLaw.output_law_source model _ returned _
    (every_returned model A K values v hv budget parsed returned hReturn).2,prepared_data]
  exact GeneralPaperEqualCopiedPipeline.epsilon model A K (input model values v hv budget parsed) hOne hBudget

end Blotto.GeneralPaperStoredParsedPreparation
