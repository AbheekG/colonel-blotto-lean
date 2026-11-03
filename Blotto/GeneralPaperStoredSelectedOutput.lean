import Blotto.GeneralPaperStoredSelectedPipeline
import Blotto.GeneralPaperEqualSelectedDraw

/-! Native coordinate height and expected random-read bounds concern the
same common-runtime constructor return, including the actual copied-input
pipeline. No claim about sharp total preparation/draw work is made here. -/
namespace Blotto.GeneralPaperStoredSelectedOutput
open MeasureTheory
open scoped ENNReal
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperEqualBitBranch (Prepared)
open GeneralPaperEqualBitBranchDraw (Trace traceLaw)
open GeneralPaperStoredSelectedDraw (Refines)
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 8192

theorem getD {n : ℕ} (row : RationalResourceArray n) (j : Fin n) : row.data.getD j.val 0 = row.allocation j := by
  have hj : j.val < row.data.size := by rw [row.size]; exact j.isLt
  simp [Array.getD,hj,RationalResourceArray.allocation]

theorem completed_coordinates {n : ℕ} (model : RationalCostModel) (A : ℕ) (outer : Installed A)
    {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ} (p : Prepared v k budget) (hRefines : Refines model A outer p)
    (trace : Trace p) (row : Array ℚ) (hOutput : (GeneralPaperStoredSelectedLaw.observed model A outer p trace).output = some row) :
    ∃ source : RationalResourceArray n,(GeneralPaperEqualBitBranchDraw.observed model A p trace).output = some source ∧
      row.size = n ∧ ∀ j : Fin n,row.getD j.val 0 = source.allocation j := by
  cases p with
  | dominant chosen heavy stored correct =>
    have hRead := (hRefines 0 (fun _ => []) []).1
    have hEq : row = stored.data := Option.some.inj (hOutput.symm.trans hRead)
    refine ⟨(GeneralPaperEqualBitBranchDraw.copyRow A stored).1,rfl,?_,?_⟩
    · rw [hEq]; exact stored.size
    · intro j
      rw [hEq,getD,GeneralPaperEqualSelectedDraw.copy_allocation]
  | grouped small sampler hK hB =>
    rw [(GeneralPaperStoredSelectedLaw.grouped_source model A outer small sampler hK hB hRefines trace).1] at hOutput
    obtain ⟨source,hSource,hData⟩ := Option.map_eq_some_iff.mp hOutput
    refine ⟨source,hSource,?_,?_⟩
    · rw [← hData]; exact source.size
    · intro j
      rw [← hData,getD]

theorem native_written_output {n b : ℕ} (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j)
    (budget : ℚ) (hBudget : 0 ≤ budget) (hHeight : RationalHeight budget b)
    (a : GeneralPaperEqualSelectedSampler.Sampler (GeneralPaperEqualNativeSampler.rounded true model W k values v hv) k budget)
    (outer : Installed a.address) (hRefines : Refines model a.address outer a.branch)
    (trace : Trace a.branch) (row : Array ℚ)
    (hOutput : (GeneralPaperStoredSelectedLaw.observed model a.address outer a.branch trace).output = some row) :
    row.size = n ∧ FullBudget (budget : ℝ) (fun j : Fin n => (row.getD j.val 0 : ℝ)) ∧
      ∀ j : Fin n,RationalHeight (row.getD j.val 0) (33554432 * (b + binaryWordWidth n + k + 10)) := by
  obtain ⟨source,hSource,hSize,hCoords⟩ := completed_coordinates model a.address outer a.branch hRefines trace row hOutput
  have hWritten := GeneralPaperEqualSelectedDraw.written_output model W k values v hv budget hBudget hHeight a trace source hSource
  have hAllocation : (fun j : Fin n => (row.getD j.val 0 : ℝ)) = source.realAllocation := by
    funext j
    rw [hCoords j]
    rfl
  refine ⟨hSize,?_,?_⟩
  · rw [hAllocation]; exact hWritten.1
  · intro j
    rw [hCoords j]
    exact hWritten.2 j

theorem native_expected_reads {n : ℕ} (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j)
    (budget : ℚ)
    (a : GeneralPaperEqualSelectedSampler.Sampler (GeneralPaperEqualNativeSampler.rounded true model W k values v hv) k budget)
    (outer : Installed a.address) (hRefines : Refines model a.address outer a.branch) :
    (∫⁻ trace, ((GeneralPaperStoredSelectedLaw.observed model a.address outer a.branch trace).reads : ℝ≥0∞)
      ∂(traceLaw a.branch : Measure (Trace a.branch))) ≤ (GeneralPaperEqualSelectedDraw.readsBound n k : ℝ≥0∞) := by
  calc
    _ = ∫⁻ trace, ((GeneralPaperEqualBitBranchDraw.observed model a.address a.branch trace).reads : ℝ≥0∞)
        ∂(traceLaw a.branch : Measure (Trace a.branch)) := by
      apply lintegral_congr_ae
      filter_upwards [] with trace
      rw [GeneralPaperStoredSelectedLaw.observed_reads_source model a.address outer a.branch hRefines trace]
    _ ≤ _ := GeneralPaperEqualSelectedDraw.expected_reads model W k values v hv budget a

theorem pipeline_written_output (model : RationalCostModel) (A K : ℕ) (p : GeneralPaperEqualInputDomain.Input model)
    (hBudget : 0 ≤ p.budget) (outer : Installed (GeneralPaperStoredSelectedPipeline.width model A K p))
    (hReturn : (GeneralPaperStoredSelectedPipeline.run model A K p).1 = some outer)
    (trace : Trace (GeneralPaperEqualCopiedPipeline.run model A K p).1.branch) (row : Array ℚ)
    (hOutput : (GeneralPaperStoredSelectedLaw.observed model (GeneralPaperStoredSelectedPipeline.width model A K p) outer
      (GeneralPaperEqualCopiedPipeline.run model A K p).1.branch trace).output = some row) :
    row.size = p.n ∧ FullBudget (p.budget : ℝ) (fun j : Fin p.n => (row.getD j.val 0 : ℝ)) ∧
      ∀ j : Fin p.n,RationalHeight (row.getD j.val 0)
        (33554432 * (rationalWordWidth p.budget + binaryWordWidth p.n + p.k + 10)) :=
  native_written_output model (GeneralPaperEqualInputDomain.word K p) p.k p.values p.selector p.correct p.budget hBudget
    (rationalHeight_of_wordWidth p.budget) _ outer
    (GeneralPaperStoredSelectedPipeline.every_returned model A K p outer hReturn) trace row hOutput

theorem pipeline_expected_reads (model : RationalCostModel) (A K : ℕ) (p : GeneralPaperEqualInputDomain.Input model)
    (outer : Installed (GeneralPaperStoredSelectedPipeline.width model A K p))
    (hReturn : (GeneralPaperStoredSelectedPipeline.run model A K p).1 = some outer) :
    (∫⁻ trace, ((GeneralPaperStoredSelectedLaw.observed model (GeneralPaperStoredSelectedPipeline.width model A K p) outer
      (GeneralPaperEqualCopiedPipeline.run model A K p).1.branch trace).reads : ℝ≥0∞)
      ∂(traceLaw (GeneralPaperEqualCopiedPipeline.run model A K p).1.branch :
        Measure (Trace (GeneralPaperEqualCopiedPipeline.run model A K p).1.branch))) ≤
      (GeneralPaperEqualSelectedDraw.readsBound p.n p.k : ℝ≥0∞) :=
  native_expected_reads model (GeneralPaperEqualInputDomain.word K p) p.k p.values p.selector p.correct p.budget _ outer
    (GeneralPaperStoredSelectedPipeline.every_returned model A K p outer hReturn)

end Blotto.GeneralPaperStoredSelectedOutput
