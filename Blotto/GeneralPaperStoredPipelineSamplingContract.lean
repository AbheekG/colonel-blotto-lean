import Blotto.GeneralPaperStoredPreparationPaperContract
import Blotto.GeneralPaperStoredPipelineDrawWork
import Blotto.GeneralPaperStoredSelectedOutput

/-! Every actual pipeline return has one common-runtime contract: exact
law, almost-sure completion, hard budgets on every completed output,
coordinate height, expected random reads and full expected draw work.
The returned memory/root is the sole executed sampler representation. -/
namespace Blotto.GeneralPaperStoredPipelineSamplingContract
open MeasureTheory
open scoped ENNReal
open GeneralPaperEqualInputDomain (Input)
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperEqualBitBranchDraw (Trace traceLaw)
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192

structure Contract (model : RationalCostModel) (A K : ℕ) (p : Input model)
    (output : Installed (GeneralPaperStoredSelectedPipeline.width model A K p)) : Prop where
  law : GeneralPaperStoredSelectedLaw.outputLaw model (GeneralPaperStoredSelectedPipeline.width model A K p) output
    (GeneralPaperEqualCopiedPipeline.run model A K p).1.branch =
      GeneralPaperEqualSelectedSampler.outputLaw model (GeneralPaperEqualCopiedPipeline.run model A K p).1
  completion : ∀ᵐ trace ∂(traceLaw (GeneralPaperEqualCopiedPipeline.run model A K p).1.branch :
      Measure (Trace (GeneralPaperEqualCopiedPipeline.run model A K p).1.branch)),
    ∃ row,(GeneralPaperStoredSelectedLaw.observed model (GeneralPaperStoredSelectedPipeline.width model A K p) output
      (GeneralPaperEqualCopiedPipeline.run model A K p).1.branch trace).output = some row
  written : 0 ≤ p.budget → ∀ trace row,
    (GeneralPaperStoredSelectedLaw.observed model (GeneralPaperStoredSelectedPipeline.width model A K p) output
      (GeneralPaperEqualCopiedPipeline.run model A K p).1.branch trace).output = some row →
    row.size = p.n ∧ FullBudget (p.budget : ℝ) (fun j : Fin p.n => (row.getD j.val 0 : ℝ)) ∧
      ∀ j : Fin p.n,RationalHeight (row.getD j.val 0)
        (33554432 * (rationalWordWidth p.budget + binaryWordWidth p.n + p.k + 10))
  expectedReads : (∫⁻ trace, ((GeneralPaperStoredSelectedLaw.observed model
      (GeneralPaperStoredSelectedPipeline.width model A K p) output
      (GeneralPaperEqualCopiedPipeline.run model A K p).1.branch trace).reads : ℝ≥0∞)
    ∂(traceLaw (GeneralPaperEqualCopiedPipeline.run model A K p).1.branch :
      Measure (Trace (GeneralPaperEqualCopiedPipeline.run model A K p).1.branch))) ≤
    (GeneralPaperEqualSelectedDraw.readsBound p.n p.k : ℝ≥0∞)
  expectedWork : (∫⁻ trace, ((GeneralPaperStoredSelectedLaw.observed model
      (GeneralPaperStoredSelectedPipeline.width model A K p) output
      (GeneralPaperEqualCopiedPipeline.run model A K p).1.branch trace).work : ℝ≥0∞)
    ∂(traceLaw (GeneralPaperEqualCopiedPipeline.run model A K p).1.branch :
      Measure (Trace (GeneralPaperEqualCopiedPipeline.run model A K p).1.branch))) ≤
    (GeneralPaperStoredPipelineDrawWork.majorant model A K p : ℝ≥0∞)

theorem every_returned (model : RationalCostModel) (A K : ℕ) (p : Input model)
    (output : Installed (GeneralPaperStoredSelectedPipeline.width model A K p))
    (hReturn : (GeneralPaperStoredSelectedPipeline.run model A K p).1 = some output) : Contract model A K p output := by
  have hRefines := GeneralPaperStoredSelectedPipeline.every_returned model A K p output hReturn
  exact ⟨GeneralPaperStoredSelectedPipeline.law model A K p output hReturn,
    GeneralPaperStoredSelectedLaw.completed_ae model _ output _ hRefines,
    fun hBudget => GeneralPaperStoredSelectedOutput.pipeline_written_output model A K p hBudget output hReturn,
    GeneralPaperStoredSelectedOutput.pipeline_expected_reads model A K p output hReturn,
    GeneralPaperStoredPipelineDrawWork.expected_work model A K p output hReturn⟩

theorem independent_players (model : RationalCostModel) (A K : ℕ) (p : Input model)
    (output : Installed (GeneralPaperStoredSelectedPipeline.width model A K p)) :
    let branch := (GeneralPaperEqualCopiedPipeline.run model A K p).1.branch
    let μ := (traceLaw branch : Measure (Trace branch))
    let decode := GeneralPaperStoredSelectedLaw.realDecode model (GeneralPaperStoredSelectedPipeline.width model A K p) output branch
    Measure.map (Prod.map decode decode) (μ.prod μ) =
      (GeneralPaperStoredSelectedLaw.outputLaw model (GeneralPaperStoredSelectedPipeline.width model A K p) output branch :
        Measure (Allocation p.n)).prod
      (GeneralPaperStoredSelectedLaw.outputLaw model (GeneralPaperStoredSelectedPipeline.width model A K p) output branch :
        Measure (Allocation p.n)) :=
  GeneralPaperStoredSelectedLaw.independent_players model _ output _

end Blotto.GeneralPaperStoredPipelineSamplingContract
