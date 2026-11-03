import Blotto.GeneralPaperFirstStoredRates

/-! Complete actual initialized/copied/stored preparation work. Existing
source creation, closure and copy prices are added to one selected two-pool
constructor and one metadata attachment. Paper-input rates retain additive
original budget and accuracy encoding lengths; no pass is repeated. -/
namespace Blotto.GeneralPaperFirstStoredWork
open GeneralPaperEqualInputDomain
open GeneralPaperUniformResourceGrowth GeneralPaperEqualUniformRateAlgebra
open GeneralPaperUnifiedDirectoryInstallation (Installed)
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

def price (model : RationalCostModel) (K : ℕ) (p : Input model) : ℕ :=
  GeneralPaperEqualFirstInputPipeline.price model (word K p) K p +
    GeneralPaperFirstStoredRates.bound model K (word K) p +
    64 * (word K p + (GeneralPaperEqualFirstInputPipeline.run model (word K p) K p).1.address + 1)

theorem work_identity (model : RationalCostModel) (A K : ℕ) (p : Input model) :
    (GeneralPaperFirstStoredPipeline.run model A K p).2 =
      (GeneralPaperEqualFirstInputPipeline.run model A K p).2 +
      (GeneralPaperStoredSelectedConstruction.run model (word K p)
        (GeneralPaperEqualFirstInputPipeline.run model A K p).1).2 +
      64 * (word K p + (GeneralPaperEqualFirstInputPipeline.run model A K p).1.address + 1) := by
  let a := (GeneralPaperEqualFirstInputPipeline.run model A K p).1
  obtain ⟨inner,hBuilt,hWork,_⟩ := GeneralPaperFirstStoredConstruction.source model
    (word K p) (word K p) p.k p.values p.selector p.correct p.budget a
  dsimp only [a] at hBuilt hWork
  simp only [GeneralPaperFirstStoredPipeline.run,hBuilt,GeneralPaperSamplerRecordInstallation.attach]
  rw [hWork]

theorem work (model : RationalCostModel) (K : ℕ) (p : Input model) :
    (GeneralPaperFirstStoredPipeline.run model (word K p) K p).2 ≤ price model K p := by
  let a := (GeneralPaperEqualFirstInputPipeline.run model (word K p) K p).1
  obtain ⟨inner,hBuilt,_,_⟩ := GeneralPaperFirstStoredConstruction.source model (word K p) (word K p)
    p.k p.values p.selector p.correct p.budget a
  dsimp only [a] at hBuilt
  have hInner := GeneralPaperFirstStoredRates.component_returned model K (word K) p inner hBuilt
  have hPrepared := GeneralPaperEqualFirstInputPipeline.work_bound model K p
  simp only [GeneralPaperFirstStoredPipeline.run,hBuilt]
  change (GeneralPaperEqualFirstInputPipeline.run model (word K p) K p).2 + inner.work +
    64 * (word K p + (GeneralPaperEqualFirstInputPipeline.run model (word K p) K p).1.address + 1) ≤ _
  unfold price
  omega

theorem returned_work (model : RationalCostModel) (K : ℕ) (p : Input model)
    (returned : Installed (GeneralPaperFirstStoredPipeline.width model (word K p) K p))
    (hReturn : (GeneralPaperFirstStoredPipeline.run model (word K p) K p).1 = some returned) :
    returned.work ≤ price model K p := by
  rw [GeneralPaperFirstStoredPipeline.every_returned_work model (word K p) K p returned hReturn]
  exact work model K p

theorem price_rate (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) (K : ℕ) :
    Bound (price model K) ledger logarithm := by
  have hL : ∀ p : Input model,1 ≤ logarithm p := logarithm_positive
  have hr : ∀ p : Input model,1 ≤ ledger p := ledger_positive
  have hOld := GeneralPaperEqualFirstInputPipeline.price_rate model hFast K
  have hConstruction := GeneralPaperFirstStoredRates.rate model hFast K (word K)
  have hSP := polylog_of_tight (word_tight K model)
  have hAP : Polylog (fun p : Input model => (GeneralPaperEqualFirstInputPipeline.run model (word K p) K p).1.address) logarithm :=
    polylog_of_tight (GeneralPaperFirstStoredRates.address_tight model K (word K))
  unfold price
  fun_prop

theorem paper_time (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) (K : ℕ) :
    ∃ C d : ℕ,∀ p : Input model,(GeneralPaperFirstStoredPipeline.run model (word K p) K p).2 ≤
      C * GeneralPaperEqualInputHeadline.inputSize p * (GeneralPaperEqualInputHeadline.paperLog p) ^ d :=
  GeneralPaperEqualInputHeadline.transfer_rate (dominated (price_rate model hFast K) (work model K))

theorem epsilon_constructed {model : RationalCostModel} (K : ℕ) (p : Input model)
    (hOne : GeneralPaperEqualInputHeadline.epsilon p < 1) (hBudget : 0 < p.budget) :
    ∃ returned : Installed (GeneralPaperFirstStoredPipeline.width model (word K p) K p),
      (GeneralPaperFirstStoredPipeline.run model (word K p) K p).1 = some returned ∧
      returned.work = (GeneralPaperFirstStoredPipeline.run model (word K p) K p).2 ∧ returned.work ≤ price model K p ∧
      let μ := GeneralPaperStoredSelectedLaw.outputLaw model (GeneralPaperFirstStoredPipeline.width model (word K p) K p) returned
        (GeneralPaperEqualFirstInputPipeline.run model (word K p) K p).1.branch
      Supported (p.budget : ℝ) μ ∧ regret p.selector.values (p.budget : ℝ) μ μ ≤ (GeneralPaperEqualInputHeadline.epsilon p : ℝ) := by
  obtain ⟨returned,hReturn,hWork,hLaw⟩ := GeneralPaperFirstStoredPipeline.epsilon_constructed model (word K p) K p hOne hBudget
  exact ⟨returned,hReturn,hWork,returned_work model K p returned hReturn,hLaw⟩


theorem source_reprice (model : RationalCostModel) (A B K : ℕ) (p : Input model) :
    (GeneralPaperEqualFirstInputPipeline.run model A K p).1 =
      (GeneralPaperEqualFirstInputPipeline.run model B K p).1 := by
  rw [GeneralPaperEqualFirstInputPipeline.data,GeneralPaperEqualFirstInputPipeline.data]

theorem work_mono (model : RationalCostModel) (A B K : ℕ) (p : Input model) (h : A ≤ B) :
    (GeneralPaperFirstStoredPipeline.run model A K p).2 ≤
      (GeneralPaperFirstStoredPipeline.run model B K p).2 := by
  have hSource : (GeneralPaperEqualFirstInputPipeline.run model A K p).2 ≤
      (GeneralPaperEqualFirstInputPipeline.run model B K p).2 := by
    rw [GeneralPaperEqualFirstInputPipeline.work,GeneralPaperEqualFirstInputPipeline.work]
    exact Nat.add_le_add_right (GeneralPaperMeasuredInitializerMonotonicity.initialization model A B K h p) _
  rw [work_identity,work_identity,source_reprice model A B K p]
  exact Nat.add_le_add_right (Nat.add_le_add_right hSource _) _

theorem actual_work (model : RationalCostModel) (K : ℕ) (p : Input model) (h : 1 ≤ word K p) :
    (GeneralPaperFirstStoredPipeline.run model 1 K p).2 ≤ price model K p :=
  (work_mono model 1 (word K p) K p h).trans (work model K p)

theorem price_actual_source (model : RationalCostModel) (K : ℕ) (p : Input model) :
    price model K p = GeneralPaperEqualFirstInputPipeline.price model (word K p) K p+
      GeneralPaperCompleteSelectedPreparationWork.bound model (word K p) (GeneralPaperEqualFirstInputPipeline.run model 1 K p).1+
      64*(word K p+(GeneralPaperEqualFirstInputPipeline.run model 1 K p).1.address+1) := by
  dsimp only [price,GeneralPaperFirstStoredRates.bound,GeneralPaperFirstStoredRates.source]
  rw [source_reprice model (word K p) 1 K p]

end Blotto.GeneralPaperFirstStoredWork
