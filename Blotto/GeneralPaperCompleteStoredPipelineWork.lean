import Blotto.GeneralPaperSelectedPreparationInputRates

/-! Complete actual initialized/copied/stored preparation work. Existing
source creation, closure and copy prices are added to one selected two-pool
constructor and one metadata attachment. Paper-input rates retain additive
original budget and accuracy encoding lengths; no pass is repeated. -/
namespace Blotto.GeneralPaperCompleteStoredPipelineWork
open GeneralPaperEqualInputDomain
open GeneralPaperUniformResourceGrowth GeneralPaperEqualUniformRateAlgebra
open GeneralPaperUnifiedDirectoryInstallation (Installed)
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

def price (model : RationalCostModel) (K : ℕ) (p : Input model) : ℕ :=
  GeneralPaperEqualCopiedPipeline.price model K p +
    GeneralPaperSelectedPreparationInputRates.bound model K (word K) p +
    64 * (word K p + (GeneralPaperEqualCopiedPipeline.run model (word K p) K p).1.address + 1)

theorem work_identity (model : RationalCostModel) (A K : ℕ) (p : Input model) :
    (GeneralPaperStoredSelectedPipeline.run model A K p).2 =
      (GeneralPaperEqualCopiedPipeline.run model A K p).2 +
      (GeneralPaperStoredSelectedConstruction.run model (word K p)
        (GeneralPaperEqualCopiedPipeline.run model A K p).1).2 +
      64 * (word K p + (GeneralPaperEqualCopiedPipeline.run model A K p).1.address + 1) := by
  let a := (GeneralPaperEqualCopiedPipeline.run model A K p).1
  obtain ⟨inner,hBuilt,hWork,_⟩ := GeneralPaperStoredSelectedConstruction.source model
    (word K p) (word K p) p.k p.values p.selector p.correct p.budget a
  dsimp only [a] at hBuilt hWork
  simp only [GeneralPaperStoredSelectedPipeline.run,hBuilt,GeneralPaperSamplerRecordInstallation.attach]
  rw [hWork]

theorem work (model : RationalCostModel) (K : ℕ) (p : Input model) :
    (GeneralPaperStoredSelectedPipeline.run model (word K p) K p).2 ≤ price model K p := by
  let a := (GeneralPaperEqualCopiedPipeline.run model (word K p) K p).1
  obtain ⟨inner,hBuilt,_,_⟩ := GeneralPaperStoredSelectedConstruction.source model (word K p) (word K p)
    p.k p.values p.selector p.correct p.budget a
  dsimp only [a] at hBuilt
  have hInner := GeneralPaperSelectedPreparationInputRates.component_returned model K (word K) p inner hBuilt
  have hPrepared := GeneralPaperEqualCopiedPipeline.work_bound model K p
  simp only [GeneralPaperStoredSelectedPipeline.run,hBuilt]
  change (GeneralPaperEqualCopiedPipeline.run model (word K p) K p).2 + inner.work +
    64 * (word K p + (GeneralPaperEqualCopiedPipeline.run model (word K p) K p).1.address + 1) ≤ _
  unfold price
  omega

theorem returned_work (model : RationalCostModel) (K : ℕ) (p : Input model)
    (returned : Installed (GeneralPaperStoredSelectedPipeline.width model (word K p) K p))
    (hReturn : (GeneralPaperStoredSelectedPipeline.run model (word K p) K p).1 = some returned) :
    returned.work ≤ price model K p := by
  rw [GeneralPaperStoredSelectedPipeline.every_returned_work model (word K p) K p returned hReturn]
  exact work model K p

theorem price_rate (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) (K : ℕ) :
    Bound (price model K) ledger logarithm := by
  have hL : ∀ p : Input model,1 ≤ logarithm p := logarithm_positive
  have hr : ∀ p : Input model,1 ≤ ledger p := ledger_positive
  have hOld := GeneralPaperEqualCopiedPipeline.price_rate model hFast K
  have hConstruction := GeneralPaperSelectedPreparationInputRates.rate model hFast K (word K)
  have hSP := polylog_of_tight (word_tight K model)
  have hAP : Polylog (fun p : Input model => (GeneralPaperEqualCopiedPipeline.run model (word K p) K p).1.address) logarithm :=
    polylog_of_tight (GeneralPaperSelectedPreparationInputRates.address_tight model K (word K))
  unfold price
  fun_prop

theorem paper_time (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) (K : ℕ) :
    ∃ C d : ℕ,∀ p : Input model,(GeneralPaperStoredSelectedPipeline.run model (word K p) K p).2 ≤
      C * GeneralPaperEqualInputHeadline.inputSize p * (GeneralPaperEqualInputHeadline.paperLog p) ^ d :=
  GeneralPaperEqualInputHeadline.transfer_rate (dominated (price_rate model hFast K) (work model K))

theorem epsilon_constructed {model : RationalCostModel} (K : ℕ) (p : Input model)
    (hOne : GeneralPaperEqualInputHeadline.epsilon p < 1) (hBudget : 0 < p.budget) :
    ∃ returned : Installed (GeneralPaperStoredSelectedPipeline.width model (word K p) K p),
      (GeneralPaperStoredSelectedPipeline.run model (word K p) K p).1 = some returned ∧
      returned.work = (GeneralPaperStoredSelectedPipeline.run model (word K p) K p).2 ∧ returned.work ≤ price model K p ∧
      let μ := GeneralPaperStoredSelectedLaw.outputLaw model (GeneralPaperStoredSelectedPipeline.width model (word K p) K p) returned
        (GeneralPaperEqualCopiedPipeline.run model (word K p) K p).1.branch
      Supported (p.budget : ℝ) μ ∧ regret p.selector.values (p.budget : ℝ) μ μ ≤ (GeneralPaperEqualInputHeadline.epsilon p : ℝ) := by
  obtain ⟨returned,hReturn,hWork,hLaw⟩ := GeneralPaperStoredSelectedPipeline.epsilon_constructed model (word K p) K p hOne hBudget
  exact ⟨returned,hReturn,hWork,returned_work model K p returned hReturn,hLaw⟩

end Blotto.GeneralPaperCompleteStoredPipelineWork
