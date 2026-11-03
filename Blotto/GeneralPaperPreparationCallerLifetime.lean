import Blotto.GeneralPaperPreparationCallerControls

/-! Complete caller data, saved prices and actual final result wrapper
coexist across stored preparation. Source creation's internal phases and
the global phase/peak calibration are joined separately. -/
namespace Blotto.GeneralPaperPreparationCallerLifetime
open GeneralPaperEqualInputDomain
open GeneralPaperMeasuredPlanLifetimeAlgebra (unit)
open GeneralPaperUniformResourceGrowth GeneralPaperEqualUniformRateAlgebra
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192

def resultWindow (model : RationalCostModel) (K : ℕ) (p : Input model) : ℕ :=
  let prepared := GeneralPaperEqualCopiedPipeline.run model (word K p) K p
  let actual := GeneralPaperStoredSelectedConstruction.run model (word K p) prepared.1
  actual.1.elim 0 (fun output => GeneralPaperResultAttachmentLifetime.window (word K p) prepared.1.address prepared.2 output)

def resultProfile (model : RationalCostModel) (K : ℕ) (p : Input model) : ℕ :=
  unit model (word K p) (GeneralPaperEqualCopiedPipeline.run model (word K p) K p).1.address
    (GeneralPaperCompleteStoredPipelineWork.price model K p)

theorem result_window_bound (model : RationalCostModel) (K : ℕ) (p : Input model) : resultWindow model K p ≤ resultProfile model K p := by
  let prepared := GeneralPaperEqualCopiedPipeline.run model (word K p) K p
  obtain ⟨inner,hBuilt,hInnerWork,_⟩ := GeneralPaperStoredSelectedConstruction.source model (word K p) (word K p)
    p.k p.values p.selector p.correct p.budget prepared.1
  have hShape := GeneralPaperCompleteStoredPipelineWork.work_identity model (word K p) K p
  have hWhole := GeneralPaperCompleteStoredPipelineWork.work model K p
  have hAttach : (GeneralPaperSamplerRecordInstallation.attach (word K p) prepared.1.address prepared.2 inner).work ≤
      GeneralPaperCompleteStoredPipelineWork.price model K p := by
    change prepared.2 + inner.work + 64 * (word K p + prepared.1.address + 1) ≤ _
    rw [hInnerWork]
    change (GeneralPaperEqualCopiedPipeline.run model (word K p) K p).2 + _ + _ ≤ _
    rw [← hShape]
    exact hWhole
  have h := GeneralPaperResultAttachmentLifetime.window_bound model (word K p) prepared.1.address prepared.2 _ inner hAttach
  dsimp only [resultWindow]
  change (GeneralPaperStoredSelectedConstruction.run model (word K p) prepared.1).1.elim 0 _ ≤ _
  rw [hBuilt]
  exact h

def window (model : RationalCostModel) (K : ℕ) (p : Input model) : ℕ :=
  GeneralPaperPreparationSourceOwners.window model K p + GeneralPaperPreparationCallerControls.window model K p + resultWindow model K p

def profile (model : RationalCostModel) (K : ℕ) (p : Input model) : ℕ :=
  GeneralPaperPreparationSourceOwners.profile model K p + GeneralPaperPreparationCallerControls.profile model K p + resultProfile model K p

theorem window_bound (model : RationalCostModel) (K : ℕ) (p : Input model) : window model K p ≤ profile model K p :=
  Nat.add_le_add (Nat.add_le_add (GeneralPaperPreparationSourceOwners.window_bound model K p)
    (GeneralPaperPreparationCallerControls.window_bound model K p)) (result_window_bound model K p)

theorem result_profile_rate (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) (K : ℕ) :
    Polylog (resultProfile model K) logarithm := by
  have hLedger : Small (ledger (model := model)) logarithm := below_ledger_small _ (fun _ => le_rfl)
  have hP := bound_small logarithm_positive (GeneralPaperCompleteStoredPipelineWork.price_rate model hFast K) hLedger
  exact GeneralPaperMeasuredPlanLifetimeRates.unit_rate model hFast (word K)
    (fun p => (GeneralPaperEqualCopiedPipeline.run model (word K p) K p).1.address)
    (GeneralPaperCompleteStoredPipelineWork.price model K) logarithm logarithm_positive (word_tight K model)
    (GeneralPaperSelectedPreparationInputRates.address_tight model K (word K)) hP

theorem profile_rate (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) (K : ℕ) :
    Bound (profile model K) ledger logarithm := by
  have hSources := GeneralPaperPreparationSourceOwners.profile_rate model K
  have hControls := GeneralPaperPreparationCallerControls.profile_rate model hFast K
  have hResult := result_profile_rate model hFast K
  have hFirst := bound_add _ _ ledger logarithm logarithm_positive hSources (rate_mono hControls ledger_positive)
  exact bound_add _ _ ledger logarithm logarithm_positive hFirst (rate_mono hResult ledger_positive)

end Blotto.GeneralPaperPreparationCallerLifetime
