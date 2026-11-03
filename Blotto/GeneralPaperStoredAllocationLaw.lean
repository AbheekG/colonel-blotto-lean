import Blotto.GeneralPaperStoredAllocationDraw

/-! The derived fair terminal-trace measure observes the actual complete
stored draw. Its continuous allocation law equals the checked source law;
source objects enter only these erased correctness statements. -/
namespace Blotto.GeneralPaperStoredAllocationLaw
open MeasureTheory
open scoped ENNReal
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperEqualRejectionTraceMeasure
open GeneralPaperStoredAllocationDraw (Refines)
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
variable {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}

noncomputable def observed (model : RationalCostModel) (A : ℕ) (installed : Installed A) (N K : ℕ) (trace : Trace N K) :=
  GeneralPaperStoredAllocationDraw.run model A installed (trace.1 + 1)
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
      (GeneralPaperEqualFullBitDraw.observed sampler.categorical model A trace).output.map RationalResourceArray.data ∧
      (observed model A installed sampler.prepared.D sampler.prepared.midpointBits trace).reads =
        (GeneralPaperEqualFullBitDraw.observed sampler.categorical model A trace).reads := by
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
      GeneralPaperEqualFullBitDraw.realDecode sampler.categorical model A trace := by
  unfold realDecode GeneralPaperEqualFullBitDraw.realDecode
  rw [(observed_source model A installed sampler hRefines trace).1]
  cases (GeneralPaperEqualFullBitDraw.observed sampler.categorical model A trace).output with
  | none => rfl
  | some row => exact array_real row

theorem output_law_source (model : RationalCostModel) (A : ℕ) (installed : Installed A)
    (sampler : GeneralPaperEqualStoredBitSampler.Sampler G l) (hRefines : Refines model A installed sampler) :
    outputLaw n model A installed sampler.prepared.D sampler.prepared.midpointBits
      (GeneralPaperEqualPreparedCache.denominator_positive sampler.prepared) =
        GeneralPaperEqualFullBitDraw.outputLaw sampler.categorical model A := by
  apply ProbabilityMeasure.toMeasure_injective
  apply Measure.map_congr
  filter_upwards [] with trace
  exact real_decode_source model A installed sampler hRefines trace

theorem every_returned_law (model : RationalCostModel) (S : ℕ) (sampler : GeneralPaperEqualStoredBitSampler.Sampler G l)
    (hA : 0 < sampler.address)
    (hCap : (GeneralPaperEqualMeasuredRetainedPlan.sampler model S sampler.address sampler).sizes.sum < 2 ^ sampler.address)
    (returned : Installed sampler.address) (hReturn : (GeneralPaperCountedSamplerInstallation.build model S sampler).values = some returned) :
    outputLaw n model sampler.address returned sampler.prepared.D sampler.prepared.midpointBits
      (GeneralPaperEqualPreparedCache.denominator_positive sampler.prepared) = GeneralPaperEqualStoredBitSampler.outputLaw sampler model :=
  output_law_source model sampler.address returned sampler (GeneralPaperStoredAllocationDraw.every_returned model S sampler hA hCap returned hReturn)

theorem completed_source (model : RationalCostModel) (A : ℕ) (installed : Installed A)
    (sampler : GeneralPaperEqualStoredBitSampler.Sampler G l) (hRefines : Refines model A installed sampler)
    (cap : ℕ) (tape : ℕ → Fin (UniformNatRejection.width sampler.prepared.D) → Bool)
    (fresh : Fin sampler.prepared.midpointBits → Bool) (row : Array ℚ)
    (hReturn : (GeneralPaperStoredAllocationDraw.run model A installed cap
      (GeneralPaperStoredBooleanRejection.blocks sampler.prepared tape) GeneralPaperBooleanFreshWord.nextList (List.ofFn fresh)).output = some row) :
    ∃ index : Fin (GeneralPaperPositiveSegmentCompaction.count l),
      (GeneralPaperEqualCachedEmission.emit sampler.prepared model (fun w => w) A index fresh).1.data = row := by
  rw [(hRefines cap tape fresh).1,GeneralPaperEqualFullBitDraw.data,Option.map_map] at hReturn
  obtain ⟨index,_,hRow⟩ := Option.map_eq_some_iff.mp hReturn
  exact ⟨index,hRow⟩

theorem completed_full_budget (model : RationalCostModel) (A : ℕ) (installed : Installed A)
    (sampler : GeneralPaperEqualStoredBitSampler.Sampler G l) (hRefines : Refines model A installed sampler)
    (hBudget : 0 ≤ sampler.prepared.budget) (hEnds : ∀ i,FullBudget 1 (l.real.P i) ∧ FullBudget 1 (l.real.Q i))
    (cap : ℕ) (tape : ℕ → Fin (UniformNatRejection.width sampler.prepared.D) → Bool)
    (fresh : Fin sampler.prepared.midpointBits → Bool) (row : Array ℚ)
    (hReturn : (GeneralPaperStoredAllocationDraw.run model A installed cap
      (GeneralPaperStoredBooleanRejection.blocks sampler.prepared tape) GeneralPaperBooleanFreshWord.nextList (List.ofFn fresh)).output = some row) :
    row.size = n ∧ FullBudget (sampler.prepared.budget : ℝ) (fun j : Fin n => (row.getD j.val 0 : ℝ)) := by
  obtain ⟨index,hRow⟩ := completed_source model A installed sampler hRefines cap tape fresh row hReturn
  rw [← hRow]
  exact ⟨(GeneralPaperEqualCachedEmission.emit sampler.prepared model (fun w => w) A index fresh).1.size,
    by rw [array_real]; exact GeneralPaperEqualCachedEmission.emit_fullBudget sampler.prepared model (fun w => w) A hBudget hEnds index fresh⟩

theorem completed_height {s b c : ℕ} (model : RationalCostModel) (A : ℕ) (installed : Installed A)
    (sampler : GeneralPaperEqualStoredBitSampler.Sampler G l) (hRefines : Refines model A installed sampler)
    (hs : 2 ≤ s) (hLottery : l.HeightAt s) (hBudget : RationalHeight sampler.prepared.budget b)
    (hc : 1 ≤ c) (hCoefficients : ∀ j,RationalHeight (sampler.prepared.routes.table.read j).2 c)
    (cap : ℕ) (tape : ℕ → Fin (UniformNatRejection.width sampler.prepared.D) → Bool)
    (fresh : Fin sampler.prepared.midpointBits → Bool) (row : Array ℚ)
    (hReturn : (GeneralPaperStoredAllocationDraw.run model A installed cap
      (GeneralPaperStoredBooleanRejection.blocks sampler.prepared tape) GeneralPaperBooleanFreshWord.nextList (List.ofFn fresh)).output = some row)
    (j : Fin n) : RationalHeight (row.getD j.val 0)
      (expressionHeightBudget (max c (GeneralPaperEqualCachedEmission.scaledHeight s sampler.prepared.midpointBits b)) 1) := by
  obtain ⟨index,hRow⟩ := completed_source model A installed sampler hRefines cap tape fresh row hReturn
  rw [← hRow]
  let emitted := (GeneralPaperEqualCachedEmission.emit sampler.prepared model (fun w => w) A index fresh).1
  have hj : j.val < emitted.data.size := by rw [emitted.size]; exact j.isLt
  have hGet : emitted.data.getD j.val 0 = emitted.allocation j := by simp [Array.getD,hj,RationalResourceArray.allocation]
  change RationalHeight (emitted.data.getD j.val 0) _
  rw [hGet]
  exact GeneralPaperEqualCachedEmission.emit_height sampler.prepared model (fun w => w) A hs hLottery hBudget hc hCoefficients index fresh j

theorem native_epsilon {n : ℕ} (bits : Bool) (model : RationalCostModel) (W S : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j)
    (eps : ℚ) (hPositive : 0 < eps) (hOne : eps < 1)
    (small : ∀ j,2 * (GeneralPaperEqualNativeSampler.rounded bits model W
      (GeneralPaperDyadicAccuracy.prepare eps).exponent values v hv).weight j ≤ 1) (budget : ℚ) (hBudget : 0 < budget)
    (hA : 0 < (GeneralPaperEqualStoredBitSampler.native bits model W (GeneralPaperDyadicAccuracy.prepare eps).exponent values v hv small budget).address)
    (hCap : (GeneralPaperEqualMeasuredRetainedPlan.sampler model S
      (GeneralPaperEqualStoredBitSampler.native bits model W (GeneralPaperDyadicAccuracy.prepare eps).exponent values v hv small budget).address
      (GeneralPaperEqualStoredBitSampler.native bits model W (GeneralPaperDyadicAccuracy.prepare eps).exponent values v hv small budget)).sizes.sum <
        2 ^ (GeneralPaperEqualStoredBitSampler.native bits model W (GeneralPaperDyadicAccuracy.prepare eps).exponent values v hv small budget).address)
    (returned : Installed (GeneralPaperEqualStoredBitSampler.native bits model W (GeneralPaperDyadicAccuracy.prepare eps).exponent values v hv small budget).address)
    (hReturn : (GeneralPaperCountedSamplerInstallation.build model S
      (GeneralPaperEqualStoredBitSampler.native bits model W (GeneralPaperDyadicAccuracy.prepare eps).exponent values v hv small budget)).values = some returned) :
    let sampler := GeneralPaperEqualStoredBitSampler.native bits model W (GeneralPaperDyadicAccuracy.prepare eps).exponent values v hv small budget
    let μ := outputLaw n model sampler.address returned sampler.prepared.D sampler.prepared.midpointBits
      (GeneralPaperEqualPreparedCache.denominator_positive sampler.prepared)
    Supported (budget : ℝ) μ ∧ regret v.values (budget : ℝ) μ μ ≤ (eps : ℝ) := by
  dsimp only
  rw [every_returned_law model S _ hA hCap returned hReturn]
  exact GeneralPaperEqualStoredBitSampler.native_epsilon bits model W values v hv eps hPositive hOne small budget hBudget

end Blotto.GeneralPaperStoredAllocationLaw
