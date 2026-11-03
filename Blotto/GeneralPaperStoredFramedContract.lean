import Blotto.GeneralPaperStoredFramedPreparation

/-! The returned frame sampler's actual common-runtime law, completion,
random reads and written rational allocations refer to its same memory.
Accuracy interpretation and native source objects occur only in proofs. -/
namespace Blotto.GeneralPaperStoredFramedContract
open MeasureTheory
open scoped ENNReal
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperBinaryAccuracy (Parsed)
open GeneralPaperStoredParsedPreparation (width prepare input)
open GeneralPaperEqualBitBranchDraw (Trace traceLaw)
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 8192

def epsilon (parsed : Parsed) : ℚ := (parsed.words.numerator.value : ℚ) / parsed.words.denominator.value

theorem epsilon_positive (parsed : Parsed) : 0 < epsilon parsed :=
  div_pos (by exact_mod_cast parsed.words.numerator.value_pos) (by exact_mod_cast parsed.words.denominator.value_pos)

theorem epsilon_numeric (parsed : Parsed) (accuracy : BinaryAccuracyInput) (hNumeric : parsed.words.numeric = accuracy) :
    epsilon parsed = (accuracy.numerator : ℚ) / accuracy.denominator := by
  have hN := congrArg BinaryAccuracyInput.numerator hNumeric
  have hD := congrArg BinaryAccuracyInput.denominator hNumeric
  change parsed.words.numerator.value = accuracy.numerator at hN
  change parsed.words.denominator.value = accuracy.denominator at hD
  rw [epsilon,hN,hD]

theorem law {n : ℕ} (model : RationalCostModel) (A K : ℕ) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j) (budget : ℚ) (parsed : Parsed)
    (inner : Installed (width model A K values v hv budget parsed))
    (hBuild : (GeneralPaperStoredParsedPreparation.run model A K values v hv budget parsed).1 = some inner)
    (prefixWork : ℕ) (suffix : List Bool) :
    GeneralPaperStoredSelectedLaw.outputLaw model (width model A K values v hv budget parsed)
      (GeneralPaperStoredFramedPreparation.finish A prefixWork inner suffix).2.1 (prepare model A K values v hv budget parsed).1.branch =
      GeneralPaperEqualSelectedSampler.outputLaw model (GeneralPaperEqualCopiedPipeline.run model A K (input model values v hv budget parsed)).1 := by
  rw [GeneralPaperStoredSelectedLaw.output_law_source model _ _ _
    (GeneralPaperStoredFramedPreparation.finished_refines model A K values v hv budget parsed inner hBuild prefixWork suffix),
    GeneralPaperStoredParsedPreparation.prepared_data]
  rfl

theorem equilibrium {n : ℕ} (model : RationalCostModel) (A K : ℕ) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j) (budget : ℚ) (hBudget : 0 < budget) (parsed : Parsed)
    (hOne : epsilon parsed < 1) (inner : Installed (width model A K values v hv budget parsed))
    (hBuild : (GeneralPaperStoredParsedPreparation.run model A K values v hv budget parsed).1 = some inner)
    (prefixWork : ℕ) (suffix : List Bool) :
    let μ := GeneralPaperStoredSelectedLaw.outputLaw model (width model A K values v hv budget parsed)
      (GeneralPaperStoredFramedPreparation.finish A prefixWork inner suffix).2.1 (prepare model A K values v hv budget parsed).1.branch
    Supported (budget : ℝ) μ ∧ regret v.values (budget : ℝ) μ μ ≤ (epsilon parsed : ℝ) := by
  dsimp only
  rw [law model A K values v hv budget parsed inner hBuild prefixWork suffix]
  exact GeneralPaperEqualCopiedPipeline.epsilon model A K (input model values v hv budget parsed) hOne hBudget

theorem completion {n : ℕ} (model : RationalCostModel) (A K : ℕ) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j) (budget : ℚ) (parsed : Parsed)
    (inner : Installed (width model A K values v hv budget parsed))
    (hBuild : (GeneralPaperStoredParsedPreparation.run model A K values v hv budget parsed).1 = some inner)
    (prefixWork : ℕ) (suffix : List Bool) :
    ∀ᵐ trace ∂(traceLaw (prepare model A K values v hv budget parsed).1.branch :
      Measure (Trace (prepare model A K values v hv budget parsed).1.branch)),
      ∃ row,(GeneralPaperStoredSelectedLaw.observed model (width model A K values v hv budget parsed)
        (GeneralPaperStoredFramedPreparation.finish A prefixWork inner suffix).2.1
        (prepare model A K values v hv budget parsed).1.branch trace).output = some row :=
  GeneralPaperStoredSelectedLaw.completed_ae model _ _ _
    (GeneralPaperStoredFramedPreparation.finished_refines model A K values v hv budget parsed inner hBuild prefixWork suffix)

theorem written_output {n b : ℕ} (model : RationalCostModel) (A K : ℕ) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j) (budget : ℚ) (hBudget : 0 ≤ budget)
    (hHeight : RationalHeight budget b) (parsed : Parsed)
    (inner : Installed (width model A K values v hv budget parsed))
    (hBuild : (GeneralPaperStoredParsedPreparation.run model A K values v hv budget parsed).1 = some inner)
    (prefixWork : ℕ) (suffix : List Bool)
    (trace : Trace (prepare model A K values v hv budget parsed).1.branch) (row : Array ℚ)
    (hOutput : (GeneralPaperStoredSelectedLaw.observed model (width model A K values v hv budget parsed)
      (GeneralPaperStoredFramedPreparation.finish A prefixWork inner suffix).2.1
      (prepare model A K values v hv budget parsed).1.branch trace).output = some row) :
    row.size = n ∧ FullBudget (budget : ℝ) (fun j : Fin n => (row.getD j.val 0 : ℝ)) ∧
      ∀ j : Fin n,RationalHeight (row.getD j.val 0) (33554432 * (b + binaryWordWidth n + parsed.exponent + 10)) :=
  GeneralPaperStoredSelectedOutput.native_written_output model (GeneralPaperEqualInputDomain.word K (input model values v hv budget parsed))
    parsed.exponent values v hv budget hBudget hHeight _ _
    (GeneralPaperStoredFramedPreparation.finished_refines model A K values v hv budget parsed inner hBuild prefixWork suffix) trace row hOutput

theorem expected_reads {n : ℕ} (model : RationalCostModel) (A K : ℕ) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j) (budget : ℚ) (parsed : Parsed)
    (inner : Installed (width model A K values v hv budget parsed))
    (hBuild : (GeneralPaperStoredParsedPreparation.run model A K values v hv budget parsed).1 = some inner)
    (prefixWork : ℕ) (suffix : List Bool) :
    (∫⁻ trace, ((GeneralPaperStoredSelectedLaw.observed model (width model A K values v hv budget parsed)
      (GeneralPaperStoredFramedPreparation.finish A prefixWork inner suffix).2.1
      (prepare model A K values v hv budget parsed).1.branch trace).reads : ℝ≥0∞)
      ∂(traceLaw (prepare model A K values v hv budget parsed).1.branch :
        Measure (Trace (prepare model A K values v hv budget parsed).1.branch))) ≤
      (GeneralPaperEqualSelectedDraw.readsBound n parsed.exponent : ℝ≥0∞) :=
  GeneralPaperStoredSelectedOutput.native_expected_reads model (GeneralPaperEqualInputDomain.word K (input model values v hv budget parsed))
    parsed.exponent values v hv budget _ _
    (GeneralPaperStoredFramedPreparation.finished_refines model A K values v hv budget parsed inner hBuild prefixWork suffix)

end Blotto.GeneralPaperStoredFramedContract
