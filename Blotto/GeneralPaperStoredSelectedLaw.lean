import Blotto.GeneralPaperStoredSelectedDraw

/-! Fair trace observations use the common actual marker dispatcher.
Its continuous law, completion and whole-player independence are derived
from the stored constructor contract, without source-directed runtime dispatch. -/
namespace Blotto.GeneralPaperStoredSelectedLaw
open MeasureTheory
open scoped ENNReal
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperEqualBitBranch (Prepared)
open GeneralPaperEqualBitBranchDraw (Trace traceLaw)
open GeneralPaperStoredSelectedDraw (Refines)
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192

noncomputable def observed {n : ℕ} (model : RationalCostModel) (A : ℕ) (outer : Installed A)
    {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ} (p : Prepared v k budget) :
    Trace p → GeneralPaperEqualBooleanTrial.Result (Array ℚ) (List Bool) :=
  match p with
  | .dominant _ _ _ _ => fun _ => GeneralPaperStoredSelectedDraw.run model A outer 0 (fun _ => []) GeneralPaperBooleanFreshWord.nextList []
  | .grouped _ sampler _ _ => fun trace =>
    GeneralPaperStoredSelectedDraw.run model A outer (trace.1 + 1)
      (GeneralPaperStoredRejectionTrace.rawBlocks sampler.prepared.D
        (GeneralPaperEqualBooleanTraceCost.tapeFor sampler.prepared.D sampler.prepared.midpointBits trace))
      GeneralPaperBooleanFreshWord.nextList
      (List.ofFn (GeneralPaperEqualRejectionTraceMeasure.scalar sampler.prepared.D sampler.prepared.midpointBits trace.1 trace.2))

noncomputable def realDecode {n : ℕ} (model : RationalCostModel) (A : ℕ) (outer : Installed A)
    {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ} (p : Prepared v k budget) (trace : Trace p) : Allocation n :=
  match (observed model A outer p trace).output with
  | none => fun _ => 0
  | some row => fun j => (row.getD j.val 0 : ℝ)

noncomputable def outputLaw {n : ℕ} (model : RationalCostModel) (A : ℕ) (outer : Installed A)
    {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ} (p : Prepared v k budget) : Mixed n :=
  (traceLaw p).map (realDecode model A outer p)

theorem measurable_decode {n : ℕ} (model : RationalCostModel) (A : ℕ) (outer : Installed A)
    {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ} (p : Prepared v k budget) :
    Measurable (realDecode model A outer p) := by
  cases p with
  | dominant chosen heavy row correct =>
    have : Countable (Trace (.dominant chosen heavy row correct : Prepared v k budget)) := by
      change Countable Unit
      infer_instance
    exact measurable_of_countable _
  | grouped small sampler hK hB =>
    have : Countable (Trace (.grouped small sampler hK hB)) := by
      change Countable (GeneralPaperEqualRejectionTraceMeasure.Trace sampler.prepared.D sampler.prepared.midpointBits)
      infer_instance
    exact measurable_of_countable _

theorem grouped_source {n : ℕ} (model : RationalCostModel) (A : ℕ) (outer : Installed A)
    {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ} (small : ∀ j,2 * v.weight j ≤ 1)
    (sampler : GeneralPaperEqualStoredBitSampler.Sampler (GeneralPaperEqualFiniteKernel.terminal v small).partition
      (GeneralPaperEqualFiniteKernel.lottery v small)) (hK : sampler.exponent = k) (hB : sampler.prepared.budget = budget)
    (hRefines : Refines model A outer (.grouped small sampler hK hB))
    (trace : GeneralPaperEqualRejectionTraceMeasure.Trace sampler.prepared.D sampler.prepared.midpointBits) :
    (observed model A outer (.grouped small sampler hK hB) trace).output =
      (GeneralPaperEqualFullBitDraw.observed sampler.categorical model sampler.address trace).output.map RationalResourceArray.data ∧
      (observed model A outer (.grouped small sampler hK hB) trace).reads =
        (GeneralPaperEqualFullBitDraw.observed sampler.categorical model sampler.address trace).reads := by
  have h := hRefines (trace.1 + 1) (GeneralPaperEqualBooleanTraceCost.tapeFor sampler.prepared.D sampler.prepared.midpointBits trace)
    (GeneralPaperEqualRejectionTraceMeasure.scalar sampler.prepared.D sampler.prepared.midpointBits trace.1 trace.2)
  rw [GeneralPaperStoredRejectionTrace.blocks_eq] at h
  exact h

theorem real_decode_source {n : ℕ} (model : RationalCostModel) (A : ℕ) (outer : Installed A)
    {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ} (p : Prepared v k budget)
    (hRefines : Refines model A outer p) (trace : Trace p) :
    realDecode model A outer p trace = GeneralPaperEqualBitBranchDraw.realDecode model A p trace := by
  cases p with
  | dominant chosen heavy row correct =>
    have h := hRefines 0 (fun _ => []) []
    simp only [realDecode,observed,h.1,GeneralPaperEqualBitBranchDraw.realDecode,
      GeneralPaperEqualBitBranchDraw.observed,GeneralPaperEqualBitBranchDraw.copy_data]
    exact GeneralPaperStoredAllocationLaw.array_real row
  | grouped small sampler hK hB =>
    unfold realDecode GeneralPaperEqualBitBranchDraw.realDecode
    rw [(grouped_source model A outer small sampler hK hB hRefines trace).1]
    change _ = GeneralPaperEqualFullBitDraw.realDecode sampler.categorical model sampler.address trace
    unfold GeneralPaperEqualFullBitDraw.realDecode
    cases (GeneralPaperEqualFullBitDraw.observed sampler.categorical model sampler.address trace).output with
    | none => rfl
    | some row => exact GeneralPaperStoredAllocationLaw.array_real row

theorem output_law_source {n : ℕ} (model : RationalCostModel) (A : ℕ) (outer : Installed A)
    {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ} (p : Prepared v k budget) (hRefines : Refines model A outer p) :
    outputLaw model A outer p = GeneralPaperEqualBitBranch.outputLaw model p := by
  rw [← GeneralPaperEqualBitBranchDraw.law model A p]
  apply ProbabilityMeasure.toMeasure_injective
  apply Measure.map_congr
  filter_upwards [] with trace
  exact real_decode_source model A outer p hRefines trace

theorem observed_reads_source {n : ℕ} (model : RationalCostModel) (A : ℕ) (outer : Installed A)
    {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ} (p : Prepared v k budget)
    (hRefines : Refines model A outer p) (trace : Trace p) :
    (observed model A outer p trace).reads = (GeneralPaperEqualBitBranchDraw.observed model A p trace).reads := by
  cases p with
  | dominant chosen heavy row correct => exact (hRefines 0 (fun _ => []) []).2
  | grouped small sampler hK hB => exact (grouped_source model A outer small sampler hK hB hRefines trace).2

theorem completed_ae {n : ℕ} (model : RationalCostModel) (A : ℕ) (outer : Installed A)
    {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ} (p : Prepared v k budget) (hRefines : Refines model A outer p) :
    ∀ᵐ trace ∂(traceLaw p : Measure (Trace p)), ∃ row, (observed model A outer p trace).output = some row := by
  cases p with
  | dominant chosen heavy row correct => exact Filter.Eventually.of_forall (fun _ => ⟨row.data,(hRefines 0 (fun _ => []) []).1⟩)
  | grouped small sampler hK hB =>
    filter_upwards [GeneralPaperEqualFullBitOutput.completed_ae sampler.categorical model sampler.address] with trace h
    obtain ⟨row,hRow⟩ := h
    rw [(grouped_source model A outer small sampler hK hB hRefines trace).1,hRow,Option.map_some]
    exact ⟨row.data,rfl⟩

theorem independent_players {n : ℕ} (model : RationalCostModel) (A : ℕ) (outer : Installed A)
    {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ} (p : Prepared v k budget) :
    let μ := (traceLaw p : Measure (Trace p))
    let f := realDecode model A outer p
    Measure.map (Prod.map f f) (μ.prod μ) =
      (outputLaw model A outer p : Measure (Allocation n)).prod (outputLaw model A outer p : Measure (Allocation n)) := by
  dsimp only
  exact (Measure.map_prod_map _ _ (measurable_decode model A outer p) (measurable_decode model A outer p)).symm

theorem completed_budget {n : ℕ} (model : RationalCostModel) (A : ℕ) (outer : Installed A)
    {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ} (p : Prepared v k budget) (hRefines : Refines model A outer p)
    (hBudget : 0 ≤ budget) (trace : Trace p) (row : Array ℚ)
    (hOutput : (observed model A outer p trace).output = some row) :
    row.size = n ∧ FullBudget (budget : ℝ) (fun j : Fin n => (row.getD j.val 0 : ℝ)) := by
  cases p with
  | dominant chosen heavy source correct =>
    have hRead := (hRefines 0 (fun _ => []) []).1
    have hEq : row = source.data := Option.some.inj (hOutput.symm.trans hRead)
    rw [hEq,GeneralPaperStoredAllocationLaw.array_real,correct]
    exact ⟨source.size,PureBoundaryEquilibria.vertex_fullBudget _ (by exact_mod_cast hBudget) chosen⟩
  | grouped small sampler hK hB =>
    rw [(grouped_source model A outer small sampler hK hB hRefines trace).1] at hOutput
    obtain ⟨source,hSource,hData⟩ := Option.map_eq_some_iff.mp hOutput
    rw [← hData,GeneralPaperStoredAllocationLaw.array_real]
    refine ⟨source.size,?_⟩
    have hb : 0 ≤ sampler.prepared.budget := by rw [hB]; exact hBudget
    have h := GeneralPaperEqualFullBitOutput.completed_budget sampler.categorical model sampler.address
      (trace.1 + 1) (GeneralPaperEqualBooleanTraceCost.tapeFor sampler.prepared.D sampler.prepared.midpointBits trace)
      (GeneralPaperEqualRejectionTraceMeasure.scalar sampler.prepared.D sampler.prepared.midpointBits trace.1 trace.2)
      hb (GeneralPaperEqualFiniteKernel.endpoints v small) source hSource
    simpa only [hB] using h

end Blotto.GeneralPaperStoredSelectedLaw
