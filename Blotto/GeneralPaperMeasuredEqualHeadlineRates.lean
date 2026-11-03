import Blotto.GeneralPaperMeasuredJointStorageCalibration

/-! Input-linear complete equal preparation time and description length.
The actual returned root/reference/work record is counted beside its RAM. -/
namespace Blotto.GeneralPaperMeasuredEqualHeadlineRates
open GeneralPaperEqualInputDomain GeneralPaperUniformResourceGrowth
open GeneralPaperEncodedScalarStorage (natBits)
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperUnifiedFieldValue (encode)
open GeneralPaperPayloadMemoryOwnership (cellSize)
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 16384

def timePrice (model : RationalCostModel) (K : ℕ) (p : Input model) : ℕ :=
  GeneralPaperCompleteStoredPipelineWork.price model K p + GeneralPaperMeasuredEqualDispatchFrame.branchPrice model p

theorem time_rate (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) (K : ℕ) :
    Bound (timePrice model K) ledger logarithm := by
  have hL : ∀ p : Input model, 1 ≤ logarithm p := logarithm_positive
  have hR : ∀ p : Input model, 1 ≤ ledger p := ledger_positive
  have hPrice := GeneralPaperCompleteStoredPipelineWork.price_rate model hFast K
  have hBudget := GeneralPaperEqualInputRates.budget_bound model
  change Bound (budgetSize (model := model)) ledger logarithm at hBudget
  have hBudgetSmall := budget_small model
  have hn := count_small model
  have hRat := GeneralPaperEqualUniformRateAlgebra.rational_bound model hFast
    (fun p : Input model => budgetSize p + 3) ledger logarithm hL (by fun_prop) (by fun_prop)
  unfold timePrice GeneralPaperMeasuredEqualDispatchFrame.branchPrice
  change Bound (fun p : Input model => GeneralPaperCompleteStoredPipelineWork.price model K p +
    (model.rat (budgetSize p + 3) + 64 * (binaryWordWidth p.n + 1))) ledger logarithm
  fun_prop

def headBits (model : RationalCostModel) (K : ℕ) (p : Input model)
    (output : Installed (GeneralPaperStoredSelectedPipeline.width model 1 K p)) : ℕ :=
  2 * GeneralPaperStoredSelectedPipeline.width model 1 K p + natBits output.work +
    64 * (GeneralPaperStoredSelectedPipeline.width model 1 K p + 1)

def headProfile (model : RationalCostModel) (K : ℕ) (p : Input model) : ℕ :=
  128 * (GeneralPaperStoredSelectedPipeline.width model 1 K p +
    natBits (GeneralPaperCompleteStoredPipelineWork.price model K p) + 1)

def descriptionProfile (model : RationalCostModel) (K : ℕ) (p : Input model) : ℕ :=
  GeneralPaperEqualSelectedDescription.footprint (GeneralPaperEqualCopiedPipeline.run model 1 K p).1 + headProfile model K p

theorem head_bound (model : RationalCostModel) (K : ℕ) (p : Input model) (hK : 1 ≤ K)
    (output : Installed (GeneralPaperStoredSelectedPipeline.width model 1 K p))
    (hReturn : (GeneralPaperStoredSelectedPipeline.run model 1 K p).1 = some output) :
    headBits model K p output ≤ headProfile model K p := by
  have hWork := GeneralPaperStoredSelectedPipeline.every_returned_work model 1 K p output hReturn
  have hPrice := (GeneralPaperMeasuredEqualWork.pipeline_mono model 1 (word K p) K
    (Nat.mul_le_mul hK (logarithm_positive p)) p).trans (GeneralPaperCompleteStoredPipelineWork.work model K p)
  rw [← hWork] at hPrice
  have hBits := GeneralPaperMeasuredUnequalCounterCapacity.bits_mono _ _ hPrice
  unfold headBits headProfile
  omega

theorem description_bound (model : RationalCostModel) (K : ℕ) (p : Input model) (hK : 1 ≤ K)
    (output : Installed (GeneralPaperStoredSelectedPipeline.width model 1 K p))
    (hReturn : (GeneralPaperStoredSelectedPipeline.run model 1 K p).1 = some output) :
    ∃ keys : Finset ℕ, (∀ key, output.memory key ≠ none → key ∈ keys) ∧
      (∑ key ∈ keys, cellSize encode output.memory key) + headBits model K p output ≤ descriptionProfile model K p := by
  obtain ⟨keys, hSupport, hMemory⟩ := GeneralPaperStoredConstructorMemoryOwnership.pipeline_returned model 1 K p output hReturn
  exact ⟨keys, hSupport, Nat.add_le_add hMemory (head_bound model K p hK output hReturn)⟩

theorem head_polylog (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) (K : ℕ) :
    Polylog (headProfile model K) logarithm := by
  have hL : ∀ p : Input model, 1 ≤ logarithm p := logarithm_positive
  have hAddress := GeneralPaperSelectedPreparationInputRates.address_tight model K (fun _ => 1)
  change Tight (fun p => GeneralPaperStoredSelectedPipeline.width model 1 K p) logarithm at hAddress
  have hWord := polylog_of_tight hAddress
  have hLedger : Small (ledger (model := model)) logarithm := below_ledger_small _ (fun _ => le_rfl)
  have hPrice := bound_small hL (GeneralPaperCompleteStoredPipelineWork.price_rate model hFast K) hLedger
  have hBits := polylog_bits _ _ hL hPrice
  unfold headProfile
  fun_prop

theorem description_rate (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) (K : ℕ) :
    Bound (descriptionProfile model K) ledger logarithm := by
  have hL : ∀ p : Input model, 1 ≤ logarithm p := logarithm_positive
  have hR : ∀ p : Input model, 1 ≤ ledger p := ledger_positive
  have hHead := at_positive_rate (head_polylog model hFast K) hR
  have hMemory := GeneralPaperSelectedPreparationInputRates.description_rate model K (fun _ => 1)
  change Bound (fun p => GeneralPaperEqualSelectedDescription.footprint (GeneralPaperEqualCopiedPipeline.run model 1 K p).1)
    ledger logarithm at hMemory
  unfold descriptionProfile
  fun_prop

end Blotto.GeneralPaperMeasuredEqualHeadlineRates
