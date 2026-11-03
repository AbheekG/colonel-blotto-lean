import Blotto.GeneralPaperNativeCursorLifetime

/-! Complete selected cursor joins prior measurement/reference/count/
layout/installation owners and returned finite RAM. Uniform original-input
space and the same-return canonical epsilon law include both cursor branches.
Outer attachment, enclosing caller sources and the full peak remain separate. -/
namespace Blotto.GeneralPaperSelectedCursorInputLifetime
open GeneralPaperEqualSelectedSampler (Sampler)
open GeneralPaperEqualMeasuredLayout (innerWidth)
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
    Bound (fun p => GeneralPaperSelectedCursorLifetime.bound model (word K p)
      (GeneralPaperEqualCopiedPipeline.run model (parent p) K p).1) ledger logarithm := by
  have hAddress := GeneralPaperSelectedPreparationInputRates.address_tight model K parent
  have hI : Tight (fun p : Input model => innerWidth (GeneralPaperEqualCopiedPipeline.run model (parent p) K p).1) logarithm := by
    obtain ⟨C,hC⟩ := hAddress
    exact ⟨C,fun p => (GeneralPaperCompleteSelectedPreparationWork.inner_width_le _).trans (hC p)⟩
  have hBi : Bound (fun p : Input model =>
      (GeneralPaperEqualMeasuredLayout.inner model (word K p) (GeneralPaperEqualCopiedPipeline.run model (parent p) K p).1).sizes.sum) ledger logarithm := by
    apply dominated (GeneralPaperSelectedPreparationInputRates.description_rate model K parent)
    intro p
    dsimp only [GeneralPaperEqualMeasuredLayout.inner]
    rw [GeneralPaperEqualMeasuredSelectedPlan.branch_sum]
    unfold GeneralPaperEqualSelectedDescription.footprint
    dsimp only [GeneralPaperSelectedPreparationInputRates.source]
    omega
  have hLedger : Small (ledger (model := model)) logarithm := by
    refine ⟨1,fun p => ?_⟩
    unfold logarithm
    omega
  exact GeneralPaperSamplerCursorLifetime.profile_rate model hFast (word K)
    (fun p => innerWidth (GeneralPaperEqualCopiedPipeline.run model (parent p) K p).1)
    (fun p => (GeneralPaperEqualMeasuredLayout.inner model (word K p)
      (GeneralPaperEqualCopiedPipeline.run model (parent p) K p).1).sizes.sum)
    ledger logarithm 168 496 logarithm_positive ledger_positive (word_tight K model) hI hBi hLedger

def combinedWindow {n : ℕ} {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ}
    (model : RationalCostModel) (S : ℕ) (source : Sampler v k budget) : ℕ :=
  GeneralPaperSelectedMeasurementInputLifetime.combinedWindow model S source + GeneralPaperSelectedCursorLifetime.window model S source

def combinedBound {n : ℕ} {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ}
    (model : RationalCostModel) (S : ℕ) (source : Sampler v k budget) : ℕ :=
  GeneralPaperSelectedMeasurementInputLifetime.combinedBound model S source + GeneralPaperSelectedCursorLifetime.bound model S source

theorem combined_window_bound {n : ℕ} (model : RationalCostModel) (W S k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j)
    (budget : ℚ) (source : Sampler (GeneralPaperEqualNativeSampler.rounded true model W k values v hv) k budget) :
    combinedWindow model S source ≤ combinedBound model S source :=
  Nat.add_le_add (GeneralPaperSelectedMeasurementInputLifetime.combined_window_bound model W S k values v hv budget source)
    (GeneralPaperSelectedCursorLifetime.native_window_bound model W S k values v hv budget source)

theorem inner_resident_coexistence {n : ℕ} (model : RationalCostModel) (W S k prefixWork : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j)
    (budget : ℚ) (source : Sampler (GeneralPaperEqualNativeSampler.rounded true model W k values v hv) k budget) :
    let output := GeneralPaperHeaderCountInstallation.finish model S (innerWidth source) prefixWork
      (GeneralPaperSelectedTemporaryOwners.directory model S source)
    ∃ keys : Finset ℕ,(∀ key,output.memory key ≠ none → key ∈ keys) ∧
      (∑ key ∈ keys,cellSize encode output.memory key) + combinedWindow model S source ≤
        (GeneralPaperEqualMeasuredLayout.inner model S source).sizes.sum + combinedBound model S source := by
  obtain ⟨keys,hSupport,hPrior⟩ := GeneralPaperSelectedMeasurementInputLifetime.inner_resident_coexistence
    model W S k prefixWork values v hv budget source
  have hCursor := GeneralPaperSelectedCursorLifetime.native_window_bound model W S k values v hv budget source
  refine ⟨keys,hSupport,?_⟩
  dsimp only [combinedWindow,combinedBound]
  omega

theorem combined_input_rate (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model)
    (K : ℕ) (parent : Input model → ℕ) :
    Bound (fun p => combinedBound model (word K p) (GeneralPaperEqualCopiedPipeline.run model (parent p) K p).1) ledger logarithm := by
  exact bound_add _ _ ledger logarithm logarithm_positive
    (GeneralPaperSelectedMeasurementInputLifetime.combined_input_rate model hFast K parent) (input_rate model hFast K parent)

theorem returned_coexistence (model : RationalCostModel) (A K : ℕ) (p : Input model)
    (returned : Installed (GeneralPaperStoredSelectedPipeline.width model A K p))
    (hReturn : (GeneralPaperStoredSelectedPipeline.run model A K p).1 = some returned) :
    ∃ keys : Finset ℕ,(∀ key,returned.memory key ≠ none → key ∈ keys) ∧
      (∑ key ∈ keys,cellSize encode returned.memory key) +
        combinedWindow model (word K p) (GeneralPaperEqualCopiedPipeline.run model A K p).1 ≤
      GeneralPaperEqualSelectedDescription.footprint (GeneralPaperEqualCopiedPipeline.run model A K p).1 +
        combinedBound model (word K p) (GeneralPaperEqualCopiedPipeline.run model A K p).1 := by
  obtain ⟨keys,hSupport,hPrior⟩ := GeneralPaperSelectedMeasurementInputLifetime.returned_coexistence model A K p returned hReturn
  have hCursor := GeneralPaperSelectedCursorLifetime.native_window_bound model (word K p) (word K p) p.k p.values p.selector p.correct p.budget
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

end Blotto.GeneralPaperSelectedCursorInputLifetime
