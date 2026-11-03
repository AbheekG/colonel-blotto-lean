import Blotto.GeneralPaperMeasuredEqualStoragePhases

/-! Saved fields of the outer original-input equal dispatcher. The branch
test, actual prepared-source/complete work and returned tag coexist. -/
namespace Blotto.GeneralPaperMeasuredEqualDispatchFrame
open GeneralPaperEqualInputDomain GeneralPaperUniformResourceGrowth
open GeneralPaperEncodedScalarStorage (fields natBits)
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 16384

def branchPrice (model : RationalCostModel) (p : Input model) : ℕ :=
  model.rat (rationalWordWidth p.budget + 3) + 64 * (binaryWordWidth p.n + 1)

def values (model : RationalCostModel) (K : ℕ) (p : Input model) : List ℕ :=
  [K, p.n, p.k, word K p, 1, (GeneralPaperEqualCopiedPipeline.run model 1 K p).1.address,
    (GeneralPaperEqualCopiedPipeline.run model 1 K p).2, (GeneralPaperStoredSelectedPipeline.run model 1 K p).2,
    branchPrice model p, (GeneralPaperStoredSelectedPipeline.run model 1 K p).2 + branchPrice model p]

def cap (model : RationalCostModel) (K : ℕ) (p : Input model) : ℕ :=
  GeneralPaperPreparationCallerControls.cap model K p + branchPrice model p + 1

def window (model : RationalCostModel) (K : ℕ) (p : Input model) : ℕ :=
  fields (word K p) (values model K p) + 128 * word K p

def profile (model : RationalCostModel) (K : ℕ) (p : Input model) : ℕ :=
  10 * (natBits (cap model K p) + word K p) + 160 * word K p

theorem values_bound (model : RationalCostModel) (K : ℕ) (p : Input model) (hK : 1 ≤ K) :
    ∀ z ∈ values model K p, z ≤ cap model K p := by
  have hW : 1 ≤ word K p := Nat.mul_le_mul hK (logarithm_positive p)
  have hp := (GeneralPaperMeasuredEqualWork.pipeline_mono model 1 (word K p) K hW p).trans
    (GeneralPaperCompleteStoredPipelineWork.work model K p)
  have hCopy := GeneralPaperMeasuredEqualWork.copied_mono model 1 (word K p) K hW p
  have hShape := GeneralPaperCompleteStoredPipelineWork.work_identity model (word K p) K p
  have hWhole := GeneralPaperCompleteStoredPipelineWork.work model K p
  have hAddress := congrArg (fun source => source.address)
    (GeneralPaperMeasuredEqualRepricing.copied_data model 1 (word K p) K p)
  intro z hz
  simp only [values, List.mem_cons, List.not_mem_nil, or_false] at hz
  unfold cap GeneralPaperPreparationCallerControls.cap
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals omega

theorem window_bound (model : RationalCostModel) (K : ℕ) (p : Input model) (hK : 1 ≤ K) :
    window model K p ≤ profile model K p := by
  have h := GeneralPaperExpressionArrayReturns.fields_mono_cap (word K p) (cap model K p)
    (values model K p) (values_bound model K p hK)
  change fields (word K p) _ ≤ 10 * (natBits (cap model K p) + word K p) + 32 * word K p at h
  unfold window profile
  omega

theorem branch_small (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) :
    Small (branchPrice model) logarithm := by
  obtain ⟨C, d, hg⟩ := hFast
  have hL : ∀ p : Input model, 1 ≤ logarithm p := logarithm_positive
  have hn := count_small model
  have hb := budget_small model
  have hp := primitive_small hg (fun p : Input model => budgetSize p + 3) logarithm hL (by fun_prop)
  change Small (fun p : Input model => model.rat (budgetSize p + 3) + 64 * (binaryWordWidth p.n + 1)) logarithm
  fun_prop

theorem cap_small (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) (K : ℕ) :
    Small (cap model K) logarithm := by
  have hL : ∀ p : Input model, 1 ≤ logarithm p := logarithm_positive
  have hWord := small_of_tight (word_tight K model) hL
  have hAddress := small_of_tight (GeneralPaperSelectedPreparationInputRates.address_tight model K (word K)) hL
  have hn := count_small model
  have hk := small_of_tight (exponent_tight model) hL
  have hLedger : Small (ledger (model := model)) logarithm := below_ledger_small _ (fun _ => le_rfl)
  have hPrice := bound_small hL (GeneralPaperCompleteStoredPipelineWork.price_rate model hFast K) hLedger
  have hBranch := branch_small model hFast
  unfold cap GeneralPaperPreparationCallerControls.cap
  fun_prop

theorem profile_polylog (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) (K : ℕ) :
    Polylog (profile model K) logarithm := by
  have hL : ∀ p : Input model, 1 ≤ logarithm p := logarithm_positive
  have hBits := polylog_bits _ _ hL (cap_small model hFast K)
  have hWord := polylog_of_tight (word_tight K model)
  unfold profile
  fun_prop

end Blotto.GeneralPaperMeasuredEqualDispatchFrame
