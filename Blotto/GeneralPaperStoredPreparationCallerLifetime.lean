import Blotto.GeneralPaperPreparationCallerLifetime

/-! Canonical stored preparation now retains literal caller data and
prices alongside every checked inner/outer preparation component and the
actual returned finite RAM. The same return carries full work and its
continuous epsilon law. Global phase/peak capacity remains separate. -/
namespace Blotto.GeneralPaperStoredPreparationCallerLifetime
open GeneralPaperEqualInputDomain
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperUnifiedFieldValue (encode)
open GeneralPaperPayloadMemoryOwnership (cellSize)
open GeneralPaperUniformResourceGrowth GeneralPaperEqualUniformRateAlgebra
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192

def window (model : RationalCostModel) (K : ℕ) (p : Input model) : ℕ :=
  GeneralPaperPreparationCallerLifetime.window model K p +
    GeneralPaperSelectedOuterInputLifetime.combinedWindow model (word K p)
      (GeneralPaperEqualCopiedPipeline.run model (word K p) K p).1

def profile (model : RationalCostModel) (K : ℕ) (p : Input model) : ℕ :=
  GeneralPaperPreparationCallerLifetime.profile model K p +
    GeneralPaperSelectedOuterInputLifetime.combinedBound model (word K p)
      (GeneralPaperEqualCopiedPipeline.run model (word K p) K p).1

theorem window_bound (model : RationalCostModel) (K : ℕ) (p : Input model) : window model K p ≤ profile model K p :=
  Nat.add_le_add (GeneralPaperPreparationCallerLifetime.window_bound model K p)
    (GeneralPaperSelectedOuterInputLifetime.combined_window_bound model (word K p) (word K p)
      p.k p.values p.selector p.correct p.budget (GeneralPaperEqualCopiedPipeline.run model (word K p) K p).1)

theorem profile_rate (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) (K : ℕ) :
    Bound (profile model K) ledger logarithm :=
  bound_add _ _ ledger logarithm logarithm_positive (GeneralPaperPreparationCallerLifetime.profile_rate model hFast K)
    (GeneralPaperSelectedOuterInputLifetime.combined_input_rate model hFast K (word K))

theorem returned_coexistence (model : RationalCostModel) (K : ℕ) (p : Input model)
    (returned : Installed (GeneralPaperStoredSelectedPipeline.width model (word K p) K p))
    (hReturn : (GeneralPaperStoredSelectedPipeline.run model (word K p) K p).1 = some returned) :
    ∃ keys : Finset ℕ,(∀ key,returned.memory key ≠ none → key ∈ keys) ∧
      (∑ key ∈ keys,cellSize encode returned.memory key) + window model K p ≤
        GeneralPaperEqualSelectedDescription.footprint (GeneralPaperEqualCopiedPipeline.run model (word K p) K p).1 + profile model K p := by
  obtain ⟨keys,hSupport,hComponents⟩ := GeneralPaperSelectedOuterInputLifetime.returned_coexistence model (word K p) K p returned hReturn
  have hCaller := GeneralPaperPreparationCallerLifetime.window_bound model K p
  refine ⟨keys,hSupport,?_⟩
  dsimp only [window,profile]
  omega

theorem paper_coexistence (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) (K : ℕ) :
    ∃ C d : ℕ,∀ (p : Input model) (returned : Installed (GeneralPaperStoredSelectedPipeline.width model (word K p) K p)),
      (GeneralPaperStoredSelectedPipeline.run model (word K p) K p).1 = some returned →
      ∃ keys : Finset ℕ,(∀ key,returned.memory key ≠ none → key ∈ keys) ∧
        (∑ key ∈ keys,cellSize encode returned.memory key) + window model K p ≤
          C * GeneralPaperEqualInputHeadline.inputSize p * (GeneralPaperEqualInputHeadline.paperLog p) ^ d := by
  have hTotal := bound_add _ _ ledger logarithm logarithm_positive
    (GeneralPaperSelectedPreparationInputRates.description_rate model K (word K)) (profile_rate model hFast K)
  obtain ⟨C,d,hSize⟩ := GeneralPaperEqualInputHeadline.transfer_rate hTotal
  refine ⟨C,d,fun p returned hReturn => ?_⟩
  obtain ⟨keys,hSupport,hWindow⟩ := returned_coexistence model K p returned hReturn
  exact ⟨keys,hSupport,hWindow.trans (hSize p)⟩

theorem epsilon_constructed {model : RationalCostModel} (K : ℕ) (p : Input model)
    (hOne : GeneralPaperEqualInputHeadline.epsilon p < 1) (hBudget : 0 < p.budget) :
    ∃ (returned : Installed (GeneralPaperStoredSelectedPipeline.width model (word K p) K p)) (keys : Finset ℕ),
      (GeneralPaperStoredSelectedPipeline.run model (word K p) K p).1 = some returned ∧
      returned.work = (GeneralPaperStoredSelectedPipeline.run model (word K p) K p).2 ∧
      returned.work ≤ GeneralPaperCompleteStoredPipelineWork.price model K p ∧
      (∀ key,returned.memory key ≠ none → key ∈ keys) ∧
      (∑ key ∈ keys,cellSize encode returned.memory key) + window model K p ≤
        GeneralPaperEqualSelectedDescription.footprint (GeneralPaperEqualCopiedPipeline.run model (word K p) K p).1 + profile model K p ∧
      let μ := GeneralPaperStoredSelectedLaw.outputLaw model (GeneralPaperStoredSelectedPipeline.width model (word K p) K p)
        returned (GeneralPaperEqualCopiedPipeline.run model (word K p) K p).1.branch
      Supported (p.budget : ℝ) μ ∧ regret p.selector.values (p.budget : ℝ) μ μ ≤
        (GeneralPaperEqualInputHeadline.epsilon p : ℝ) := by
  obtain ⟨returned,hReturn,hWork,hCost,hLaw⟩ := GeneralPaperCompleteStoredPipelineWork.epsilon_constructed K p hOne hBudget
  obtain ⟨keys,hSupport,hWindow⟩ := returned_coexistence model K p returned hReturn
  exact ⟨returned,keys,hReturn,hWork,hCost,hSupport,hWindow,hLaw⟩

end Blotto.GeneralPaperStoredPreparationCallerLifetime
