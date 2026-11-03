import Blotto.GeneralPaperSelectedOuterLifetime

/-! Complete selected outer attachment joins every prior measured inner
preparation window and returned finite RAM. Actual executed prices derive
metadata widths. Original-input soft space and the canonical epsilon law
hold on the same return; caller retained sources/global peak remain open. -/
namespace Blotto.GeneralPaperSelectedOuterInputLifetime
open GeneralPaperEqualSelectedSampler (Sampler)
open GeneralPaperUnifiedFieldValue (encode)
open GeneralPaperPayloadMemoryOwnership (cellSize)
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperEqualInputDomain
open GeneralPaperUniformResourceGrowth GeneralPaperEqualUniformRateAlgebra
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192

theorem input_rate (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model)
    (K : ℕ) (parent : Input model → ℕ) :
    Bound (fun p => GeneralPaperSelectedOuterLifetime.bound model (word K p)
      (GeneralPaperEqualCopiedPipeline.run model (parent p) K p).1) ledger logarithm := by
  let A := fun p : Input model => (GeneralPaperEqualCopiedPipeline.run model (parent p) K p).1.address
  let P := fun p : Input model => GeneralPaperCompleteSelectedPreparationWork.bound model (word K p)
    (GeneralPaperEqualCopiedPipeline.run model (parent p) K p).1
  have hA : Tight A logarithm := GeneralPaperSelectedPreparationInputRates.address_tight model K parent
  have hP : Bound P ledger logarithm := GeneralPaperSelectedPreparationInputRates.rate model hFast K parent
  have hLedger : Small (ledger (model := model)) logarithm := by
    refine ⟨1,fun p => ?_⟩
    unfold logarithm
    omega
  have hPrice := bound_small logarithm_positive hP hLedger
  have hOuter := GeneralPaperOuterConstructionLifetime.profile_rate model hFast (word K) A P ledger logarithm
    logarithm_positive ledger_positive (word_tight K model) hA hPrice hLedger
  have hUnit := GeneralPaperMeasuredPlanLifetimeRates.unit_rate model hFast (word K) A P logarithm
    logarithm_positive (word_tight K model) hA hPrice
  change Bound (fun p => GeneralPaperOuterConstructionLifetime.profile model (word K p) (A p) (P p) +
    GeneralPaperMeasuredPlanLifetimeAlgebra.unit model (word K p) (A p) (P p)) ledger logarithm
  exact bound_add _ _ ledger logarithm logarithm_positive hOuter (rate_mono hUnit ledger_positive)

def combinedWindow {n : ℕ} {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ}
    (model : RationalCostModel) (S : ℕ) (source : Sampler v k budget) : ℕ :=
  GeneralPaperSelectedCursorInputLifetime.combinedWindow model S source + GeneralPaperSelectedOuterLifetime.window model S source

def combinedBound {n : ℕ} {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ}
    (model : RationalCostModel) (S : ℕ) (source : Sampler v k budget) : ℕ :=
  GeneralPaperSelectedCursorInputLifetime.combinedBound model S source + GeneralPaperSelectedOuterLifetime.bound model S source

theorem combined_window_bound {n : ℕ} (model : RationalCostModel) (W S k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j)
    (budget : ℚ) (source : Sampler (GeneralPaperEqualNativeSampler.rounded true model W k values v hv) k budget) :
    combinedWindow model S source ≤ combinedBound model S source :=
  Nat.add_le_add (GeneralPaperSelectedCursorInputLifetime.combined_window_bound model W S k values v hv budget source)
    (GeneralPaperSelectedOuterLifetime.window_bound model W S k values v hv budget source)

theorem combined_input_rate (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model)
    (K : ℕ) (parent : Input model → ℕ) :
    Bound (fun p => combinedBound model (word K p) (GeneralPaperEqualCopiedPipeline.run model (parent p) K p).1) ledger logarithm := by
  exact bound_add _ _ ledger logarithm logarithm_positive
    (GeneralPaperSelectedCursorInputLifetime.combined_input_rate model hFast K parent) (input_rate model hFast K parent)

theorem returned_coexistence (model : RationalCostModel) (A K : ℕ) (p : Input model)
    (returned : Installed (GeneralPaperStoredSelectedPipeline.width model A K p))
    (hReturn : (GeneralPaperStoredSelectedPipeline.run model A K p).1 = some returned) :
    ∃ keys : Finset ℕ,(∀ key,returned.memory key ≠ none → key ∈ keys) ∧
      (∑ key ∈ keys,cellSize encode returned.memory key) +
        combinedWindow model (word K p) (GeneralPaperEqualCopiedPipeline.run model A K p).1 ≤
      GeneralPaperEqualSelectedDescription.footprint (GeneralPaperEqualCopiedPipeline.run model A K p).1 +
        combinedBound model (word K p) (GeneralPaperEqualCopiedPipeline.run model A K p).1 := by
  obtain ⟨keys,hSupport,hPrior⟩ := GeneralPaperSelectedCursorInputLifetime.returned_coexistence model A K p returned hReturn
  have hCursor := GeneralPaperSelectedOuterLifetime.window_bound model (word K p) (word K p) p.k p.values p.selector p.correct p.budget
    (GeneralPaperEqualCopiedPipeline.run model A K p).1
  refine ⟨keys,hSupport,?_⟩
  dsimp only [combinedWindow,combinedBound]
  omega

theorem paper_coexistence (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model)
    (K : ℕ) (parent : Input model → ℕ) :
    ∃ C d : ℕ,∀ (p : Input model) (returned : Installed (GeneralPaperStoredSelectedPipeline.width model (parent p) K p)),
      (GeneralPaperStoredSelectedPipeline.run model (parent p) K p).1 = some returned →
      ∃ keys : Finset ℕ,(∀ key,returned.memory key ≠ none → key ∈ keys) ∧
        (∑ key ∈ keys,cellSize encode returned.memory key) +
          combinedWindow model (word K p) (GeneralPaperEqualCopiedPipeline.run model (parent p) K p).1 ≤
        C * GeneralPaperEqualInputHeadline.inputSize p * (GeneralPaperEqualInputHeadline.paperLog p) ^ d := by
  have hTotal := bound_add _ _ ledger logarithm logarithm_positive
    (GeneralPaperSelectedPreparationInputRates.description_rate model K parent) (combined_input_rate model hFast K parent)
  obtain ⟨C,d,hSize⟩ := GeneralPaperEqualInputHeadline.transfer_rate hTotal
  refine ⟨C,d,fun p returned hReturn => ?_⟩
  obtain ⟨keys,hSupport,hWindow⟩ := returned_coexistence model (parent p) K p returned hReturn
  exact ⟨keys,hSupport,hWindow.trans (hSize p)⟩

theorem epsilon_constructed {model : RationalCostModel} (K : ℕ) (p : Input model)
    (hOne : GeneralPaperEqualInputHeadline.epsilon p < 1) (hBudget : 0 < p.budget) :
    ∃ (returned : Installed (GeneralPaperStoredSelectedPipeline.width model (word K p) K p)) (keys : Finset ℕ),
      (GeneralPaperStoredSelectedPipeline.run model (word K p) K p).1 = some returned ∧
      returned.work = (GeneralPaperStoredSelectedPipeline.run model (word K p) K p).2 ∧
      returned.work ≤ GeneralPaperCompleteStoredPipelineWork.price model K p ∧
      (∀ key,returned.memory key ≠ none → key ∈ keys) ∧
      (∑ key ∈ keys,cellSize encode returned.memory key) +
        combinedWindow model (word K p) (GeneralPaperEqualCopiedPipeline.run model (word K p) K p).1 ≤
      GeneralPaperEqualSelectedDescription.footprint (GeneralPaperEqualCopiedPipeline.run model (word K p) K p).1 +
        combinedBound model (word K p) (GeneralPaperEqualCopiedPipeline.run model (word K p) K p).1 ∧
      let μ := GeneralPaperStoredSelectedLaw.outputLaw model (GeneralPaperStoredSelectedPipeline.width model (word K p) K p)
        returned (GeneralPaperEqualCopiedPipeline.run model (word K p) K p).1.branch
      Supported (p.budget : ℝ) μ ∧ regret p.selector.values (p.budget : ℝ) μ μ ≤
        (GeneralPaperEqualInputHeadline.epsilon p : ℝ) := by
  obtain ⟨returned,hReturn,hWork,hCost,hLaw⟩ := GeneralPaperCompleteStoredPipelineWork.epsilon_constructed K p hOne hBudget
  obtain ⟨keys,hSupport,hWindow⟩ := returned_coexistence model (word K p) K p returned hReturn
  exact ⟨returned,keys,hReturn,hWork,hCost,hSupport,hWindow,hLaw⟩

end Blotto.GeneralPaperSelectedOuterInputLifetime
