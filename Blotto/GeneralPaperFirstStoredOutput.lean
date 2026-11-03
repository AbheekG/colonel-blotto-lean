import Blotto.GeneralPaperFirstStoredCapacity

/-! Exact stored-runtime read counts and every completed output row for the
corrected actual sampler, including the direct initialized installed return. -/
namespace Blotto.GeneralPaperFirstStoredOutput
open MeasureTheory
open scoped ENNReal
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperEqualBitBranchDraw (Trace traceLaw)
open GeneralPaperStoredSelectedDraw (Refines)
open GeneralPaperStoredSelectedOutput (completed_coordinates)
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

theorem native_written_output {n b : ℕ} (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j)
    (budget : ℚ) (hBudget : 0 ≤ budget) (hHeight : RationalHeight budget b)
    (a : GeneralPaperEqualSelectedSampler.Sampler (GeneralPaperEqualFirstNativeFacts.rounded true model W k values v hv) k budget)
    (outer : Installed a.address) (hRefines : Refines model a.address outer a.branch)
    (trace : Trace a.branch) (row : Array ℚ)
    (hOutput : (GeneralPaperStoredSelectedLaw.observed model a.address outer a.branch trace).output = some row) :
    row.size = n ∧ FullBudget (budget : ℝ) (fun j : Fin n => (row.getD j.val 0 : ℝ)) ∧
      ∀ j : Fin n,RationalHeight (row.getD j.val 0) (GeneralPaperEqualBitDrawRates.word n (k+1) b) := by
  obtain ⟨source,hSource,hSize,hCoords⟩ := completed_coordinates model a.address outer a.branch hRefines trace row hOutput
  have hHeightOut := GeneralPaperEqualFirstBitOutput.completed_height model W a.address k values v hv budget hHeight a.branch trace source hSource
  have hBudgetOut := GeneralPaperEqualBitBranchDraw.completed_budget model a.address a.branch hBudget trace source hSource
  have hAllocation : (fun j : Fin n => (row.getD j.val 0 : ℝ)) = source.realAllocation := by
    funext j
    rw [hCoords j]
    rfl
  refine ⟨hSize,?_,?_⟩
  · rw [hAllocation]; exact hBudgetOut
  · intro j
    rw [hCoords j]
    exact hHeightOut j

theorem native_expected_reads {n : ℕ} (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j)
    (budget : ℚ)
    (a : GeneralPaperEqualSelectedSampler.Sampler (GeneralPaperEqualFirstNativeFacts.rounded true model W k values v hv) k budget)
    (outer : Installed a.address) (hRefines : Refines model a.address outer a.branch) :
    (∫⁻ trace, ((GeneralPaperStoredSelectedLaw.observed model a.address outer a.branch trace).reads : ℝ≥0∞)
      ∂(traceLaw a.branch : Measure (Trace a.branch))) ≤ (GeneralPaperEqualFirstBitSampling.readsBound n k : ℝ≥0∞) := by
  calc
    _ = ∫⁻ trace, ((GeneralPaperEqualBitBranchDraw.observed model a.address a.branch trace).reads : ℝ≥0∞)
        ∂(traceLaw a.branch : Measure (Trace a.branch)) := by
      apply lintegral_congr_ae
      filter_upwards [] with trace
      rw [GeneralPaperStoredSelectedLaw.observed_reads_source model a.address outer a.branch hRefines trace]
    _ ≤ _ := GeneralPaperEqualFirstBitSampling.expected_reads model W a.address k values v hv budget a.branch

theorem pipeline_written_output (model : RationalCostModel) (A K : ℕ) (p : GeneralPaperEqualInputDomain.Input model)
    (hBudget : 0 ≤ p.budget) (outer : Installed (GeneralPaperFirstStoredPipeline.width model A K p))
    (hReturn : (GeneralPaperFirstStoredPipeline.run model A K p).1 = some outer)
    (trace : Trace (GeneralPaperEqualFirstInputPipeline.run model A K p).1.branch) (row : Array ℚ)
    (hOutput : (GeneralPaperStoredSelectedLaw.observed model (GeneralPaperFirstStoredPipeline.width model A K p) outer
      (GeneralPaperEqualFirstInputPipeline.run model A K p).1.branch trace).output = some row) :
    row.size = p.n ∧ FullBudget (p.budget : ℝ) (fun j : Fin p.n => (row.getD j.val 0 : ℝ)) ∧
      ∀ j : Fin p.n,RationalHeight (row.getD j.val 0)
        (GeneralPaperEqualBitDrawRates.word p.n (p.k+1) (rationalWordWidth p.budget)) :=
  native_written_output model (GeneralPaperEqualInputDomain.word K p) p.k p.values p.selector p.correct p.budget hBudget
    (rationalHeight_of_wordWidth p.budget) _ outer
    (GeneralPaperFirstStoredPipeline.every_returned model A K p outer hReturn) trace row hOutput

theorem pipeline_expected_reads (model : RationalCostModel) (A K : ℕ) (p : GeneralPaperEqualInputDomain.Input model)
    (outer : Installed (GeneralPaperFirstStoredPipeline.width model A K p))
    (hReturn : (GeneralPaperFirstStoredPipeline.run model A K p).1 = some outer) :
    (∫⁻ trace, ((GeneralPaperStoredSelectedLaw.observed model (GeneralPaperFirstStoredPipeline.width model A K p) outer
      (GeneralPaperEqualFirstInputPipeline.run model A K p).1.branch trace).reads : ℝ≥0∞)
      ∂(traceLaw (GeneralPaperEqualFirstInputPipeline.run model A K p).1.branch :
        Measure (Trace (GeneralPaperEqualFirstInputPipeline.run model A K p).1.branch))) ≤
      (GeneralPaperEqualFirstBitSampling.readsBound p.n p.k : ℝ≥0∞) :=
  native_expected_reads model (GeneralPaperEqualInputDomain.word K p) p.k p.values p.selector p.correct p.budget _ outer
    (GeneralPaperFirstStoredPipeline.every_returned model A K p outer hReturn)


end Blotto.GeneralPaperFirstStoredOutput
