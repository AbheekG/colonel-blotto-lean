import Blotto.GeneralPaperPayloadInstallationLifetime

/-! Finite paper-RAM ownership of the actual returned inner/outer/selected
sampler. Count expansion uses the original measured extent; same-memory
outer installation adds only its own extent. The final map is one memory,
and its payload can coexist with the complete selected layout-owner window. -/
namespace Blotto.GeneralPaperStoredConstructorMemoryOwnership
open GeneralPaperPayloadMemoryOwnership (Bounded cellSize)
open GeneralPaperUnifiedFieldValue (encode)
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperEqualSelectedSampler (Sampler)
open GeneralPaperEqualInputDomain
open GeneralPaperUniformResourceGrowth GeneralPaperEqualUniformRateAlgebra
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192

theorem sampler_prefix {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
    (model : RationalCostModel) (S A start : ℕ) (source : GeneralPaperEqualStoredBitSampler.Sampler G l)
    (rest : List (GeneralPaperSequentialLayout.Region A)) (returned : Installed A)
    (hReturn : (GeneralPaperCountedSamplerInstallation.run model S A source
      ((GeneralPaperMeasuredBlockLayout.run model S A start (GeneralPaperEqualMeasuredRetainedPlan.sampler model S A source)).1 ++ rest)).values = some returned) :
    Bounded encode returned.memory (GeneralPaperEqualMeasuredRetainedPlan.sampler model S A source).sizes.sum := by
  obtain ⟨hParsed,_,hSafe,hCovered⟩ := GeneralPaperSamplerRecordCursor.success model S A start source rest
  simp only [GeneralPaperCountedSamplerInstallation.run,hParsed] at hReturn
  have hEq := Option.some.inj hReturn
  rw [← hEq]
  exact GeneralPaperUnifiedInstallationOwnership.counted_install model S A start _ _ _ hSafe hCovered

theorem dominant_prefix {n : ℕ} (model : RationalCostModel) (S A start chosen : ℕ) (row : RationalResourceArray n)
    (rest : List (GeneralPaperSequentialLayout.Region A)) (returned : Installed A)
    (hReturn : (GeneralPaperStoredDominantInstallation.run model S A chosen row
      ((GeneralPaperMeasuredBlockLayout.run model S A start (GeneralPaperStoredDominantCursor.plan model S A chosen row)).1 ++ rest)).values = some returned) :
    Bounded encode returned.memory (GeneralPaperStoredDominantCursor.plan model S A chosen row).sizes.sum := by
  obtain ⟨hParsed,_,hSafe,hCovered⟩ := GeneralPaperStoredDominantCursor.success model S A start chosen row rest
  simp only [GeneralPaperStoredDominantInstallation.run,hParsed] at hReturn
  have hEq := Option.some.inj hReturn
  rw [← hEq]
  exact GeneralPaperUnifiedInstallationOwnership.counted_install model S A start _ _ _ hSafe hCovered

theorem grouped_returned {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
    (model : RationalCostModel) (S : ℕ) (source : GeneralPaperEqualStoredBitSampler.Sampler G l)
    (hCap : (GeneralPaperEqualMeasuredRetainedPlan.sampler model S source.address source).sizes.sum < 2 ^ source.address)
    (returned : Installed (source.address + 1))
    (hReturn : (GeneralPaperStoredGroupedOuterConstruction.run model S source).values = some returned) :
    Bounded encode returned.memory
      ((GeneralPaperEqualMeasuredRetainedPlan.sampler model S source.address source).sizes.sum +
        (GeneralPaperEqualMeasuredSelectedPlan.header model S (source.address + 1)).sizes.sum) := by
  have hI := GeneralPaperStoredNativeConstruction.address_positive source
  obtain ⟨inner,hInner,_,_,_,_⟩ := GeneralPaperCountedSamplerInstallation.sampler_prefix model S source.address 0 source [] hI
    (by simpa only [Nat.zero_add] using hCap)
  have hMemory := sampler_prefix model S source.address 0 source [] inner hInner
  simp only [List.append_nil] at hInner
  have hInnerActual : (GeneralPaperCountedSamplerInstallation.run model S source.address source
      (GeneralPaperStoredGroupedOuterConstruction.layout model S source).inner).values = some inner := hInner
  simp only [GeneralPaperStoredGroupedOuterConstruction.run,hInnerActual,
    GeneralPaperStoredGroupedOuterConstruction.fields_source] at hReturn
  have hEq := Option.some.inj hReturn
  rw [← hEq]
  exact GeneralPaperUnifiedInstallationOwnership.outer_attachment model S source.address (source.address + 1)
    (GeneralPaperStoredGroupedOuterConstruction.layout model S source).boundary _ _ inner hMemory 1

theorem dominant_returned {n : ℕ} (model : RationalCostModel) (S A chosen : ℕ) (row : RationalResourceArray n)
    (hA : 0 < A) (hCap : (GeneralPaperStoredDominantCursor.plan model S A chosen row).sizes.sum < 2 ^ A)
    (returned : Installed A) (hReturn : (GeneralPaperStoredDominantOuterConstruction.run model S A chosen row).values = some returned) :
    Bounded encode returned.memory ((GeneralPaperStoredDominantCursor.plan model S A chosen row).sizes.sum +
      (GeneralPaperEqualMeasuredSelectedPlan.header model S A).sizes.sum) := by
  obtain ⟨inner,hInner,_,_,_,_⟩ := GeneralPaperStoredDominantInstallation.source model S A 0 chosen row [] hA
    (by simpa only [Nat.zero_add] using hCap)
  have hMemory := dominant_prefix model S A 0 chosen row [] inner hInner
  simp only [List.append_nil] at hInner
  have hInnerActual : (GeneralPaperStoredDominantInstallation.run model S A chosen row
      (GeneralPaperStoredDominantOuterConstruction.layout model S A chosen row).inner).values = some inner := hInner
  simp only [GeneralPaperStoredDominantOuterConstruction.run,hInnerActual,
    GeneralPaperStoredDominantOuterConstruction.fields_source] at hReturn
  have hEq := Option.some.inj hReturn
  rw [← hEq]
  exact GeneralPaperUnifiedInstallationOwnership.outer_attachment model S A A
    (GeneralPaperStoredDominantOuterConstruction.layout model S A chosen row).boundary _ _ inner hMemory 0

theorem selected_returned {n : ℕ} (model : RationalCostModel) (W S k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j)
    (budget : ℚ) (source : Sampler (GeneralPaperEqualNativeSampler.rounded true model W k values v hv) k budget)
    (returned : Installed source.address) (hReturn : (GeneralPaperStoredSelectedConstruction.run model S source).1 = some returned) :
    Bounded encode returned.memory (GeneralPaperEqualSelectedDescription.footprint source) := by
  have hInnerCap := GeneralPaperEqualMeasuredLayout.inner_capacity model W S k values v hv budget source
  have hTotalCap := GeneralPaperEqualMeasuredLayout.total_capacity model W S k values v hv budget source
  have hWidths := GeneralPaperEqualMeasuredLayout.widths_positive source
  have hExtent : (GeneralPaperEqualMeasuredLayout.inner model S source).sizes.sum +
      (GeneralPaperEqualMeasuredLayout.outer model S source).sizes.sum = GeneralPaperEqualSelectedDescription.footprint source := by
    dsimp only [GeneralPaperEqualMeasuredLayout.inner,GeneralPaperEqualMeasuredLayout.outer]
    rw [GeneralPaperEqualMeasuredSelectedPlan.branch_sum,GeneralPaperEqualMeasuredSelectedPlan.header_sum]
    rfl
  rw [← hExtent]
  cases source with
  | mk branch A hAddress =>
    cases branch with
    | dominant chosen heavy row correct =>
      change (GeneralPaperStoredDominantOuterConstruction.run model S A chosen.val row).values = some returned at hReturn
      exact dominant_returned model S A chosen.val row hWidths.2 hInnerCap returned hReturn
    | grouped small sampler hK hB =>
      dsimp only [GeneralPaperEqualSelectedSampler.baseReference] at hAddress
      subst A
      obtain ⟨actual,hActual,_,_,_⟩ := GeneralPaperStoredGroupedOuterConstruction.source model S sampler hInnerCap hTotalCap
      have hMemory := grouped_returned model S sampler hInnerCap actual hActual
      simp only [GeneralPaperStoredSelectedConstruction.run,hActual,Option.map_some,
        GeneralPaperStoredSelectedConstruction.recast] at hReturn
      have hEq := Option.some.inj hReturn
      rw [← hEq]
      exact hMemory

theorem pipeline_returned (model : RationalCostModel) (A K : ℕ) (p : Input model)
    (returned : Installed (GeneralPaperStoredSelectedPipeline.width model A K p))
    (hReturn : (GeneralPaperStoredSelectedPipeline.run model A K p).1 = some returned) :
    Bounded encode returned.memory (GeneralPaperEqualSelectedDescription.footprint (GeneralPaperEqualCopiedPipeline.run model A K p).1) := by
  let a := (GeneralPaperEqualCopiedPipeline.run model A K p).1
  obtain ⟨inner,hBuilt,_,_⟩ := GeneralPaperStoredSelectedConstruction.source model (word K p) (word K p)
    p.k p.values p.selector p.correct p.budget a
  dsimp only [a] at hBuilt
  have hMemory := selected_returned model (word K p) (word K p) p.k p.values p.selector p.correct p.budget _ inner hBuilt
  simp only [GeneralPaperStoredSelectedPipeline.run,hBuilt] at hReturn
  have hEq := Option.some.inj hReturn
  rw [← hEq]
  exact hMemory

theorem paper_ram (model : RationalCostModel) (K : ℕ) (parent : Input model → ℕ) :
    ∃ C d : ℕ,∀ (p : Input model) (returned : Installed (GeneralPaperStoredSelectedPipeline.width model (parent p) K p)),
      (GeneralPaperStoredSelectedPipeline.run model (parent p) K p).1 = some returned →
      Bounded encode returned.memory (C * GeneralPaperEqualInputHeadline.inputSize p * (GeneralPaperEqualInputHeadline.paperLog p) ^ d) := by
  obtain ⟨C,d,hSize⟩ := GeneralPaperEqualInputHeadline.transfer_rate
    (GeneralPaperSelectedPreparationInputRates.description_rate model K parent)
  exact ⟨C,d,fun p returned hReturn =>
    GeneralPaperPayloadMemoryOwnership.mono encode _ _ _ (pipeline_returned model (parent p) K p returned hReturn) (hSize p)⟩

theorem layout_coexistence (model : RationalCostModel) (A K : ℕ) (p : Input model)
    (returned : Installed (GeneralPaperStoredSelectedPipeline.width model A K p))
    (hReturn : (GeneralPaperStoredSelectedPipeline.run model A K p).1 = some returned) :
    ∃ keys : Finset ℕ,(∀ key,returned.memory key ≠ none → key ∈ keys) ∧
      (∑ key ∈ keys,cellSize encode returned.memory key) +
        GeneralPaperSelectedLayoutLifetime.window model (word K p) (GeneralPaperEqualCopiedPipeline.run model A K p).1 ≤
      GeneralPaperEqualSelectedDescription.footprint (GeneralPaperEqualCopiedPipeline.run model A K p).1 +
        GeneralPaperSelectedLayoutLifetime.bound model (word K p) (GeneralPaperEqualCopiedPipeline.run model A K p).1 := by
  obtain ⟨keys,hSupport,hPayload⟩ := pipeline_returned model A K p returned hReturn
  have hLayout := GeneralPaperSelectedLayoutLifetime.window_bound model (word K p) (word K p) p.k p.values p.selector p.correct p.budget
    (GeneralPaperEqualCopiedPipeline.run model A K p).1
  exact ⟨keys,hSupport,Nat.add_le_add hPayload hLayout⟩

theorem paper_layout_coexistence (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model)
    (K : ℕ) (parent : Input model → ℕ) :
    ∃ C d : ℕ,∀ (p : Input model) (returned : Installed (GeneralPaperStoredSelectedPipeline.width model (parent p) K p)),
      (GeneralPaperStoredSelectedPipeline.run model (parent p) K p).1 = some returned →
      ∃ keys : Finset ℕ,(∀ key,returned.memory key ≠ none → key ∈ keys) ∧
        (∑ key ∈ keys,cellSize encode returned.memory key) +
          GeneralPaperSelectedLayoutLifetime.window model (word K p) (GeneralPaperEqualCopiedPipeline.run model (parent p) K p).1 ≤
        C * GeneralPaperEqualInputHeadline.inputSize p * (GeneralPaperEqualInputHeadline.paperLog p) ^ d := by
  have hTotal := bound_add _ _ ledger logarithm logarithm_positive
    (GeneralPaperSelectedPreparationInputRates.description_rate model K parent)
    (GeneralPaperSelectedLayoutLifetimeRates.input_rate model hFast K parent)
  obtain ⟨C,d,hSize⟩ := GeneralPaperEqualInputHeadline.transfer_rate hTotal
  refine ⟨C,d,fun p returned hReturn => ?_⟩
  obtain ⟨keys,hSupport,hWindow⟩ := layout_coexistence model (parent p) K p returned hReturn
  exact ⟨keys,hSupport,hWindow.trans (hSize p)⟩

theorem epsilon_constructed {model : RationalCostModel} (K : ℕ) (p : Input model)
    (hOne : GeneralPaperEqualInputHeadline.epsilon p < 1) (hBudget : 0 < p.budget) :
    ∃ returned : Installed (GeneralPaperStoredSelectedPipeline.width model (word K p) K p),
      (GeneralPaperStoredSelectedPipeline.run model (word K p) K p).1 = some returned ∧
      returned.work = (GeneralPaperStoredSelectedPipeline.run model (word K p) K p).2 ∧
      returned.work ≤ GeneralPaperCompleteStoredPipelineWork.price model K p ∧
      Bounded encode returned.memory (GeneralPaperEqualSelectedDescription.footprint (GeneralPaperEqualCopiedPipeline.run model (word K p) K p).1) ∧
      GeneralPaperSelectedLayoutLifetime.window model (word K p) (GeneralPaperEqualCopiedPipeline.run model (word K p) K p).1 ≤
        GeneralPaperSelectedLayoutLifetime.bound model (word K p) (GeneralPaperEqualCopiedPipeline.run model (word K p) K p).1 ∧
      let μ := GeneralPaperStoredSelectedLaw.outputLaw model (GeneralPaperStoredSelectedPipeline.width model (word K p) K p)
        returned (GeneralPaperEqualCopiedPipeline.run model (word K p) K p).1.branch
      Supported (p.budget : ℝ) μ ∧ regret p.selector.values (p.budget : ℝ) μ μ ≤
        (GeneralPaperEqualInputHeadline.epsilon p : ℝ) := by
  obtain ⟨returned,hReturn,hWork,hCost,hLayout,hLaw⟩ := GeneralPaperSelectedLayoutLifetimeRates.epsilon_constructed K p hOne hBudget
  exact ⟨returned,hReturn,hWork,hCost,pipeline_returned model (word K p) K p returned hReturn,hLayout,hLaw⟩

end Blotto.GeneralPaperStoredConstructorMemoryOwnership
