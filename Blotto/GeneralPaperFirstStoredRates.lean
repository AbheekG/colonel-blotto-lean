import Blotto.GeneralPaperFirstStoredPipeline

/-! Sharp input-domain rates for complete actual selected construction.
Retained description size keeps the sole original-budget encoding additive.
The parent initialization reference may vary without changing these source
data bounds; its own processing price remains in the existing pipeline. -/
namespace Blotto.GeneralPaperFirstStoredRates
open GeneralPaperEqualInputDomain
open GeneralPaperUniformResourceGrowth GeneralPaperEqualUniformRateAlgebra
open GeneralPaperUnifiedDirectoryInstallation (Installed)
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192

def source (model : RationalCostModel) (K : ℕ) (parent : Input model → ℕ) (p : Input model) :=
  (GeneralPaperEqualFirstInputPipeline.run model (parent p) K p).1

def bound (model : RationalCostModel) (K : ℕ) (parent : Input model → ℕ) (p : Input model) : ℕ :=
  GeneralPaperCompleteSelectedPreparationWork.bound model (word K p) (source model K parent p)

theorem description_rate (model : RationalCostModel) (K : ℕ) (parent : Input model → ℕ) :
    Bound (fun p => GeneralPaperEqualSelectedDescription.footprint (source model K parent p)) ledger logarithm := by
  have hL : ∀ p : Input model,1 ≤ logarithm p := logarithm_positive
  have hr : ∀ p : Input model,1 ≤ ledger p := ledger_positive
  have hn : Bound (fun p : Input model => p.n) ledger logarithm := pointwise _ _ _ 1 (fun p => by unfold ledger; omega)
  have hb : Bound (fun p : Input model => rationalWordWidth p.budget) ledger logarithm := pointwise _ _ _ 1 (fun p => by unfold ledger budgetSize; omega)
  have hnSmall := count_small model
  have hbSmall : Small (fun p : Input model => rationalWordWidth p.budget) logarithm := budget_small model
  have hkTight := exponent_tight model
  have hkP := polylog_of_tight hkTight
  have hkSmall := small_of_tight hkTight hL
  have hMajor : Bound (fun p : Input model => 2 * GeneralPaperEqualDescriptionRates.paperBound p.n (p.k+1) (rationalWordWidth p.budget)) ledger logarithm := by
    dsimp only [GeneralPaperEqualDescriptionRates.paperBound,GeneralPaperEqualNativeRetainedStorage.short,
      GeneralPaperEqualBitDrawRates.log,GeneralPaperEqualBitDrawRates.word,GeneralPaperEqualBitDrawRates.size]
    fun_prop (config := {maxSteps := 50000})
  exact dominated hMajor (fun p => GeneralPaperEqualFirstSelectedDescription.paper_bound model (word K p) p.k
    p.values p.selector p.correct p.budget (source model K parent p))

theorem address_tight (model : RationalCostModel) (K : ℕ) (parent : Input model → ℕ) :
    Tight (fun p => (source model K parent p).address) logarithm := by
  have hL : ∀ p : Input model,1 ≤ logarithm p := logarithm_positive
  have hnSmall := count_small model
  have hbSmall : Small (fun p : Input model => rationalWordWidth p.budget) logarithm := budget_small model
  have hkTight := exponent_tight model
  have hkSmall := small_of_tight hkTight hL
  have hBig : Small (fun p : Input model => p.n + GeneralPaperEqualBitDrawRates.word p.n p.k (rationalWordWidth p.budget) + 32) logarithm := by
    dsimp only [GeneralPaperEqualBitDrawRates.word,GeneralPaperEqualBitDrawRates.size]
    fun_prop
  obtain ⟨C,hC⟩ := hBig
  refine ⟨2 * C + 3,fun p => ?_⟩
  have h := GeneralPaperEqualSelectedSampler.address_bound (source model K parent p)
  have hw := hC p
  have hp := hL p
  change (source model K parent p).address ≤ 2 * GeneralPaperEqualBitDrawRates.log p.n p.k (rationalWordWidth p.budget) + 1 at h
  unfold GeneralPaperEqualBitDrawRates.log at h
  nlinarith only [h,hw,hp]

theorem rate (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) (K : ℕ) (parent : Input model → ℕ) :
    Bound (bound model K parent) ledger logarithm :=
  GeneralPaperCompleteSelectedPreparationWork.rate model hFast (word K) ledger logarithm
    (fun p : Input model => p.n) (fun p => p.k)
    (fun p => GeneralPaperEqualFirstNativeFacts.rounded true model (word K p) p.k p.values p.selector p.correct)
    (fun p => p.budget) (source model K parent) logarithm_positive ledger_positive (word_tight K model)
    (address_tight model K parent) (description_rate model K parent)

theorem component_work (model : RationalCostModel) (K : ℕ) (parent : Input model → ℕ) (p : Input model) :
    (GeneralPaperStoredSelectedConstruction.run model (word K p) (source model K parent p)).2 ≤ bound model K parent p :=
  GeneralPaperFirstStoredConstruction.work model (word K p) (word K p) p.k p.values p.selector p.correct p.budget (source model K parent p)

theorem component_returned (model : RationalCostModel) (K : ℕ) (parent : Input model → ℕ) (p : Input model)
    (returned : Installed (source model K parent p).address)
    (hReturn : (GeneralPaperStoredSelectedConstruction.run model (word K p) (source model K parent p)).1 = some returned) :
    returned.work ≤ bound model K parent p :=
  GeneralPaperFirstStoredConstruction.returned_work model (word K p) (word K p) p.k p.values p.selector p.correct p.budget
    (source model K parent p) returned hReturn

end Blotto.GeneralPaperFirstStoredRates
