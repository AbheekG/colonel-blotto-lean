import Blotto.GeneralPaperSelectedTemporaryOwners

/-! Actual selected temporary-owner windows inherit uniform paper-input
soft space bounds. The original budget and input encodings remain additive.
The same constructed installed return keeps its complete work and canonical
law; this component does not claim internal frames or installed memory have
already been combined into a full preparation peak. -/
namespace Blotto.GeneralPaperSelectedTemporaryOwnerRates
open GeneralPaperUniformResourceGrowth GeneralPaperEqualUniformRateAlgebra
open GeneralPaperEqualSelectedSampler (Sampler)
open GeneralPaperEqualInputDomain
open GeneralPaperSelectedTemporaryOwners
open GeneralPaperUnifiedDirectoryInstallation (Installed)
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192

theorem rate {α : Type*} (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model)
    (S r L n k : α → ℕ) (v : (x : α) → RationalFieldSelector (n x)) (budget : α → ℚ)
    (sources : (x : α) → Sampler (v x) (k x) (budget x))
    (hL : ∀ x,1 ≤ L x) (hr : ∀ x,1 ≤ r x) (hS : Tight S L)
    (hA : Tight (fun x => (sources x).address) L)
    (hExtent : Bound (fun x => GeneralPaperEqualSelectedDescription.footprint (sources x)) r L)
    (hrSmall : Small r L) : Bound (fun x => bound model (S x) (sources x)) r L := by
  have hI : Tight (fun x => GeneralPaperEqualMeasuredLayout.innerWidth (sources x)) L := by
    obtain ⟨C,hC⟩ := hA
    exact ⟨C,fun x => (GeneralPaperCompleteSelectedPreparationWork.inner_width_le (sources x)).trans (hC x)⟩
  have hBi : Bound (fun x => (GeneralPaperEqualMeasuredLayout.inner model (S x) (sources x)).sizes.sum) r L := by
    apply dominated hExtent
    intro x
    dsimp only [GeneralPaperEqualMeasuredLayout.inner]
    rw [GeneralPaperEqualMeasuredSelectedPlan.branch_sum]
    unfold GeneralPaperEqualSelectedDescription.footprint
    omega
  have hBo : Bound (fun x => (GeneralPaperEqualMeasuredLayout.outer model (S x) (sources x)).sizes.sum) r L := by
    apply dominated hExtent
    intro x
    dsimp only [GeneralPaperEqualMeasuredLayout.outer]
    rw [GeneralPaperEqualMeasuredSelectedPlan.header_sum]
    unfold GeneralPaperEqualSelectedDescription.footprint
    omega
  have hWork := GeneralPaperCompleteSelectedPreparationWork.rate model hFast S r L n k v budget sources hL hr hS hA hExtent
  have hPrice := bound_small hL hWork hrSmall
  have hPools := GeneralPaperMeasuredDirectoryStorageRates.two_pool_rate S
    (fun x => GeneralPaperEqualMeasuredLayout.innerWidth (sources x)) (fun x => (sources x).address)
    (fun x => (GeneralPaperEqualMeasuredLayout.inner model (S x) (sources x)).sizes.sum)
    (fun x => (GeneralPaperEqualMeasuredLayout.outer model (S x) (sources x)).sizes.sum)
    (fun x => GeneralPaperCompleteSelectedPreparationWork.bound model (S x) (sources x))
    (fun x => GeneralPaperCompleteSelectedPreparationWork.bound model (S x) (sources x))
    (fun x => GeneralPaperCompleteSelectedPreparationWork.bound model (S x) (sources x))
    r L hL hr hS hI hA hBi hBo hPrice hPrice hPrice
  have hDirectory := GeneralPaperMeasuredDirectoryStorageRates.count_rate model hFast S
    (fun x => GeneralPaperEqualMeasuredLayout.innerWidth (sources x))
    (fun x => (GeneralPaperEqualMeasuredLayout.inner model (S x) (sources x)).sizes.sum)
    r L hL hr hS hI hBi hrSmall
  simpa only [bound] using bound_add _ _ r L hL hPools hDirectory

theorem input_rate (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model)
    (K : ℕ) (parent : Input model → ℕ) :
    Bound (fun p => bound model (word K p) (GeneralPaperEqualCopiedPipeline.run model (parent p) K p).1) ledger logarithm := by
  have hLedger : Small (ledger (model := model)) logarithm := by
    refine ⟨1,fun p => ?_⟩
    unfold logarithm
    omega
  exact rate model hFast (word K) ledger logarithm (fun p => p.n) (fun p => p.k)
    (fun p => GeneralPaperEqualNativeSampler.rounded true model (word K p) p.k p.values p.selector p.correct)
    (fun p => p.budget) (fun p => (GeneralPaperEqualCopiedPipeline.run model (parent p) K p).1)
    logarithm_positive ledger_positive (word_tight K model)
    (GeneralPaperSelectedPreparationInputRates.address_tight model K parent)
    (GeneralPaperSelectedPreparationInputRates.description_rate model K parent) hLedger

theorem actual_input_rate (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model)
    (K : ℕ) (parent : Input model → ℕ) :
    Bound (fun p => window model (word K p) (GeneralPaperEqualCopiedPipeline.run model (parent p) K p).1) ledger logarithm := by
  apply dominated (input_rate model hFast K parent)
  intro p
  exact window_bound model (word K p) (word K p) p.k p.values p.selector p.correct p.budget _

theorem paper_space (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model)
    (K : ℕ) (parent : Input model → ℕ) :
    ∃ C d : ℕ,∀ p : Input model,
      window model (word K p) (GeneralPaperEqualCopiedPipeline.run model (parent p) K p).1 ≤
        C * GeneralPaperEqualInputHeadline.inputSize p * (GeneralPaperEqualInputHeadline.paperLog p) ^ d :=
  GeneralPaperEqualInputHeadline.transfer_rate (actual_input_rate model hFast K parent)

theorem epsilon_constructed {model : RationalCostModel} (K : ℕ) (p : Input model)
    (hOne : GeneralPaperEqualInputHeadline.epsilon p < 1) (hBudget : 0 < p.budget) :
    ∃ returned : Installed (GeneralPaperStoredSelectedPipeline.width model (word K p) K p),
      (GeneralPaperStoredSelectedPipeline.run model (word K p) K p).1 = some returned ∧
      returned.work = (GeneralPaperStoredSelectedPipeline.run model (word K p) K p).2 ∧
      returned.work ≤ GeneralPaperCompleteStoredPipelineWork.price model K p ∧
      window model (word K p) (GeneralPaperEqualCopiedPipeline.run model (word K p) K p).1 ≤
        bound model (word K p) (GeneralPaperEqualCopiedPipeline.run model (word K p) K p).1 ∧
      let μ := GeneralPaperStoredSelectedLaw.outputLaw model (GeneralPaperStoredSelectedPipeline.width model (word K p) K p)
        returned (GeneralPaperEqualCopiedPipeline.run model (word K p) K p).1.branch
      Supported (p.budget : ℝ) μ ∧ regret p.selector.values (p.budget : ℝ) μ μ ≤
        (GeneralPaperEqualInputHeadline.epsilon p : ℝ) := by
  obtain ⟨returned,hReturn,hWork,hCost,hLaw⟩ := GeneralPaperCompleteStoredPipelineWork.epsilon_constructed K p hOne hBudget
  exact ⟨returned,hReturn,hWork,hCost,
    window_bound model (word K p) (word K p) p.k p.values p.selector p.correct p.budget _,hLaw⟩

end Blotto.GeneralPaperSelectedTemporaryOwnerRates
