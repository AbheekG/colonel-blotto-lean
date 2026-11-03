import Blotto.GeneralPaperStoredGroupedOuterNative

/-! Fair terminal traces observe the actual mixed-width outer draw.
Its output law, completion and hard-budget guarantees follow from complete
finite output/read refinement; source values are erased proof parameters. -/
namespace Blotto.GeneralPaperStoredGroupedOuterLaw
open MeasureTheory
open scoped ENNReal
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperEqualRejectionTraceMeasure
open GeneralPaperStoredGroupedOuterDraw (Refines)
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
variable {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}

noncomputable def observed (model : RationalCostModel) (A : ℕ) (installed : Installed A) (N K : ℕ) (trace : Trace N K) :=
  GeneralPaperStoredGroupedOuterDraw.run model A installed (trace.1 + 1)
    (GeneralPaperStoredRejectionTrace.rawBlocks N (GeneralPaperEqualBooleanTraceCost.tapeFor N K trace))
    GeneralPaperBooleanFreshWord.nextList (List.ofFn (scalar N K trace.1 trace.2))

noncomputable def realDecode (n : ℕ) (model : RationalCostModel) (A : ℕ) (installed : Installed A) (N K : ℕ) (trace : Trace N K) : Allocation n :=
  match (observed model A installed N K trace).output with
  | none => fun _ => 0
  | some row => fun j => (row.getD j.val 0 : ℝ)

noncomputable def outputLaw (n : ℕ) (model : RationalCostModel) (A : ℕ) (installed : Installed A) (N K : ℕ) (hN : 0 < N) : Mixed n :=
  (law N K hN).map (realDecode n model A installed N K)

theorem observed_source (model : RationalCostModel) (A : ℕ) (installed : Installed A)
    (sampler : GeneralPaperEqualStoredBitSampler.Sampler G l) (hRefines : Refines model A installed sampler)
    (trace : Trace sampler.prepared.D sampler.prepared.midpointBits) :
    (observed model A installed sampler.prepared.D sampler.prepared.midpointBits trace).output =
      (GeneralPaperEqualFullBitDraw.observed sampler.categorical model sampler.address trace).output.map RationalResourceArray.data ∧
      (observed model A installed sampler.prepared.D sampler.prepared.midpointBits trace).reads =
        (GeneralPaperEqualFullBitDraw.observed sampler.categorical model sampler.address trace).reads := by
  have h := hRefines (trace.1 + 1) (GeneralPaperEqualBooleanTraceCost.tapeFor sampler.prepared.D sampler.prepared.midpointBits trace)
    (scalar sampler.prepared.D sampler.prepared.midpointBits trace.1 trace.2)
  rw [GeneralPaperStoredRejectionTrace.blocks_eq] at h
  exact h

theorem array_real (row : RationalResourceArray n) :
    (fun j : Fin n => (row.data.getD j.val 0 : ℝ)) = row.realAllocation := by
  funext j
  have hj : j.val < row.data.size := by rw [row.size]; exact j.isLt
  simp only [RationalResourceArray.realAllocation,RationalResourceArray.allocation]
  simp [Array.getD,hj]

theorem real_decode_source (model : RationalCostModel) (A : ℕ) (installed : Installed A)
    (sampler : GeneralPaperEqualStoredBitSampler.Sampler G l) (hRefines : Refines model A installed sampler)
    (trace : Trace sampler.prepared.D sampler.prepared.midpointBits) :
    realDecode n model A installed sampler.prepared.D sampler.prepared.midpointBits trace =
      GeneralPaperEqualFullBitDraw.realDecode sampler.categorical model sampler.address trace := by
  unfold realDecode GeneralPaperEqualFullBitDraw.realDecode
  rw [(observed_source model A installed sampler hRefines trace).1]
  cases (GeneralPaperEqualFullBitDraw.observed sampler.categorical model sampler.address trace).output with
  | none => rfl
  | some row => exact array_real row

theorem output_law_source (model : RationalCostModel) (A : ℕ) (installed : Installed A)
    (sampler : GeneralPaperEqualStoredBitSampler.Sampler G l) (hRefines : Refines model A installed sampler) :
    outputLaw n model A installed sampler.prepared.D sampler.prepared.midpointBits
      (GeneralPaperEqualPreparedCache.denominator_positive sampler.prepared) =
        GeneralPaperEqualFullBitDraw.outputLaw sampler.categorical model sampler.address := by
  apply ProbabilityMeasure.toMeasure_injective
  apply Measure.map_congr
  filter_upwards [] with trace
  exact real_decode_source model A installed sampler hRefines trace

theorem completed_source (model : RationalCostModel) (A : ℕ) (installed : Installed A)
    (sampler : GeneralPaperEqualStoredBitSampler.Sampler G l) (hRefines : Refines model A installed sampler)
    (cap : ℕ) (tape : ℕ → Fin (UniformNatRejection.width sampler.prepared.D) → Bool)
    (fresh : Fin sampler.prepared.midpointBits → Bool) (row : Array ℚ)
    (hReturn : (GeneralPaperStoredGroupedOuterDraw.run model A installed cap
      (GeneralPaperStoredBooleanRejection.blocks sampler.prepared tape) GeneralPaperBooleanFreshWord.nextList (List.ofFn fresh)).output = some row) :
    ∃ index : Fin (GeneralPaperPositiveSegmentCompaction.count l),
      (GeneralPaperEqualCachedEmission.emit sampler.prepared model (fun w => w) sampler.address index fresh).1.data = row := by
  rw [(hRefines cap tape fresh).1,GeneralPaperEqualFullBitDraw.data,Option.map_map] at hReturn
  obtain ⟨index,_,hRow⟩ := Option.map_eq_some_iff.mp hReturn
  exact ⟨index,hRow⟩

theorem completed_full_budget (model : RationalCostModel) (A : ℕ) (installed : Installed A)
    (sampler : GeneralPaperEqualStoredBitSampler.Sampler G l) (hRefines : Refines model A installed sampler)
    (hBudget : 0 ≤ sampler.prepared.budget) (hEnds : ∀ i,FullBudget 1 (l.real.P i) ∧ FullBudget 1 (l.real.Q i))
    (cap : ℕ) (tape : ℕ → Fin (UniformNatRejection.width sampler.prepared.D) → Bool)
    (fresh : Fin sampler.prepared.midpointBits → Bool) (row : Array ℚ)
    (hReturn : (GeneralPaperStoredGroupedOuterDraw.run model A installed cap
      (GeneralPaperStoredBooleanRejection.blocks sampler.prepared tape) GeneralPaperBooleanFreshWord.nextList (List.ofFn fresh)).output = some row) :
    row.size = n ∧ FullBudget (sampler.prepared.budget : ℝ) (fun j : Fin n => (row.getD j.val 0 : ℝ)) := by
  obtain ⟨index,hRow⟩ := completed_source model A installed sampler hRefines cap tape fresh row hReturn
  rw [← hRow]
  exact ⟨(GeneralPaperEqualCachedEmission.emit sampler.prepared model (fun w => w) sampler.address index fresh).1.size,
    by rw [array_real]; exact GeneralPaperEqualCachedEmission.emit_fullBudget sampler.prepared model (fun w => w) sampler.address hBudget hEnds index fresh⟩

theorem completed_height {s b c : ℕ} (model : RationalCostModel) (A : ℕ) (installed : Installed A)
    (sampler : GeneralPaperEqualStoredBitSampler.Sampler G l) (hRefines : Refines model A installed sampler)
    (hs : 2 ≤ s) (hLottery : l.HeightAt s) (hBudget : RationalHeight sampler.prepared.budget b)
    (hc : 1 ≤ c) (hCoefficients : ∀ j,RationalHeight (sampler.prepared.routes.table.read j).2 c)
    (cap : ℕ) (tape : ℕ → Fin (UniformNatRejection.width sampler.prepared.D) → Bool)
    (fresh : Fin sampler.prepared.midpointBits → Bool) (row : Array ℚ)
    (hReturn : (GeneralPaperStoredGroupedOuterDraw.run model A installed cap
      (GeneralPaperStoredBooleanRejection.blocks sampler.prepared tape) GeneralPaperBooleanFreshWord.nextList (List.ofFn fresh)).output = some row)
    (j : Fin n) : RationalHeight (row.getD j.val 0)
      (expressionHeightBudget (max c (GeneralPaperEqualCachedEmission.scaledHeight s sampler.prepared.midpointBits b)) 1) := by
  obtain ⟨index,hRow⟩ := completed_source model A installed sampler hRefines cap tape fresh row hReturn
  rw [← hRow]
  let emitted := (GeneralPaperEqualCachedEmission.emit sampler.prepared model (fun w => w) sampler.address index fresh).1
  have hj : j.val < emitted.data.size := by rw [emitted.size]; exact j.isLt
  have hGet : emitted.data.getD j.val 0 = emitted.allocation j := by simp [Array.getD,hj,RationalResourceArray.allocation]
  change RationalHeight (emitted.data.getD j.val 0) _
  rw [hGet]
  exact GeneralPaperEqualCachedEmission.emit_height sampler.prepared model (fun w => w) sampler.address hs hLottery hBudget hc hCoefficients index fresh j


theorem completed_ae (model : RationalCostModel) (A : ℕ) (outer : Installed A)
    (sampler : GeneralPaperEqualStoredBitSampler.Sampler G l) (hRefines : Refines model A outer sampler) :
    ∀ᵐ trace ∂(law sampler.prepared.D sampler.prepared.midpointBits
      (GeneralPaperEqualPreparedCache.denominator_positive sampler.prepared) : Measure (Trace sampler.prepared.D sampler.prepared.midpointBits)),
      ∃ row, (observed model A outer sampler.prepared.D sampler.prepared.midpointBits trace).output = some row := by
  filter_upwards [GeneralPaperEqualFullBitOutput.completed_ae sampler.categorical model sampler.address] with trace h
  obtain ⟨row,hRow⟩ := h
  rw [(observed_source model A outer sampler hRefines trace).1,hRow,Option.map_some]
  exact ⟨row.data,rfl⟩

theorem expected_reads_exact (model : RationalCostModel) (A : ℕ) (outer : Installed A)
    (sampler : GeneralPaperEqualStoredBitSampler.Sampler G l) (hRefines : Refines model A outer sampler) :
    (∫⁻ trace, ((observed model A outer sampler.prepared.D sampler.prepared.midpointBits trace).reads : ℝ≥0∞)
      ∂(law sampler.prepared.D sampler.prepared.midpointBits
        (GeneralPaperEqualPreparedCache.denominator_positive sampler.prepared) : Measure (Trace sampler.prepared.D sampler.prepared.midpointBits))) =
      ENNReal.ofReal ((UniformNatRejection.width sampler.prepared.D : ℝ) /
        (UniformNatRejection.acceptance sampler.prepared.D : ℝ) + sampler.prepared.midpointBits) := by
  calc
    _ = ∫⁻ trace, ((GeneralPaperEqualFullBitDraw.observed sampler.categorical model sampler.address trace).reads : ℝ≥0∞)
        ∂(law sampler.prepared.D sampler.prepared.midpointBits
          (GeneralPaperEqualPreparedCache.denominator_positive sampler.prepared) : Measure (Trace sampler.prepared.D sampler.prepared.midpointBits)) := by
      apply lintegral_congr_ae
      filter_upwards [] with trace
      rw [(observed_source model A outer sampler hRefines trace).2]
    _ = _ := GeneralPaperEqualFullBitOutput.expected_reads_exact sampler.categorical model sampler.address

theorem independent_traces (model : RationalCostModel) (A : ℕ) (outer : Installed A)
    (N K : ℕ) (hN : 0 < N) :
    let μ := (law N K hN : Measure (Trace N K))
    let f := realDecode n model A outer N K
    Measure.map (Prod.map f f) (μ.prod μ) =
      (outputLaw n model A outer N K hN : Measure (Allocation n)).prod
        (outputLaw n model A outer N K hN : Measure (Allocation n)) := by
  dsimp only
  exact (Measure.map_prod_map _ _ (measurable_of_countable _) (measurable_of_countable _)).symm

theorem completed_row (model : RationalCostModel) (A : ℕ) (outer : Installed A)
    (sampler : GeneralPaperEqualStoredBitSampler.Sampler G l) (hRefines : Refines model A outer sampler)
    (cap : ℕ) (tape : ℕ → Fin (UniformNatRejection.width sampler.prepared.D) → Bool)
    (fresh : Fin sampler.prepared.midpointBits → Bool) (row : Array ℚ)
    (hReturn : (GeneralPaperStoredGroupedOuterDraw.run model A outer cap
      (GeneralPaperStoredBooleanRejection.blocks sampler.prepared tape)
      GeneralPaperBooleanFreshWord.nextList (List.ofFn fresh)).output = some row) :
    ∃ source : RationalResourceArray n,
      (GeneralPaperEqualFullBitDraw.run sampler.categorical model sampler.address cap tape fresh).output = some source ∧ source.data = row := by
  exact Option.map_eq_some_iff.mp ((hRefines cap tape fresh).1.symm.trans hReturn)

end Blotto.GeneralPaperStoredGroupedOuterLaw
