import Blotto.GeneralPaperPreparationSourceOwners

/-! Actual canonical stored-pipeline caller fields, including pre-copy,
copied, built and final/partial prices. Exact executed work identities
derive every encoded-width condition. No supplied work bound executes. -/
namespace Blotto.GeneralPaperPreparationCallerControls
open GeneralPaperEqualInputDomain
open GeneralPaperEncodedScalarStorage
open GeneralPaperUniformResourceGrowth GeneralPaperEqualUniformRateAlgebra
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192

def controls (model : RationalCostModel) (K : ℕ) (p : Input model) : List ℕ :=
  let S := word K p
  let source := GeneralPaperEqualCopiedPipeline.run model S K p
  let built := GeneralPaperStoredSelectedConstruction.run model S source.1
  [S,K,p.n,p.k,source.1.address,(GeneralPaperEqualSelectedPipeline.run model S K p).2,
    source.2,built.2,source.2 + built.2,(GeneralPaperStoredSelectedPipeline.run model S K p).2]

def cap (model : RationalCostModel) (K : ℕ) (p : Input model) : ℕ :=
  word K p + K + p.n + p.k + (GeneralPaperEqualCopiedPipeline.run model (word K p) K p).1.address +
    GeneralPaperCompleteStoredPipelineWork.price model K p + 1

theorem fields_bounded (model : RationalCostModel) (K : ℕ) (p : Input model) :
    ∀ value ∈ controls model K p,value ≤ cap model K p := by
  have hCopy := GeneralPaperEqualCopiedPipeline.copy_work_exact model (word K p) K p
  have hShape := GeneralPaperCompleteStoredPipelineWork.work_identity model (word K p) K p
  have hWhole := GeneralPaperCompleteStoredPipelineWork.work model K p
  intro value hv
  simp only [controls,List.mem_cons,List.not_mem_nil,or_false] at hv
  unfold cap
  rcases hv with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> omega

def window (model : RationalCostModel) (K : ℕ) (p : Input model) : ℕ :=
  fields (word K p) (controls model K p) + 224 * word K p

def profile (model : RationalCostModel) (K : ℕ) (p : Input model) : ℕ :=
  10 * (natBits (cap model K p) + word K p) + 256 * word K p

theorem window_bound (model : RationalCostModel) (K : ℕ) (p : Input model) : window model K p ≤ profile model K p := by
  have h := fields_bound (word K p) (natBits (cap model K p)) (controls model K p)
    (fun value hv => Nat.add_le_add_left (binaryWordWidth_mono (fields_bounded model K p value hv)) 1)
  change fields (word K p) (controls model K p) ≤ 10 * (natBits (cap model K p) + word K p) + 32 * word K p at h
  unfold window profile
  omega

theorem profile_rate (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) (K : ℕ) :
    Polylog (profile model K) logarithm := by
  have hL : ∀ p : Input model,1 ≤ logarithm p := logarithm_positive
  have hWord := polylog_of_tight (word_tight K model)
  have hWordSmall := small_of_tight (word_tight K model) hL
  have hAddress := small_of_tight (GeneralPaperSelectedPreparationInputRates.address_tight model K (word K)) hL
  have hCount := count_small model
  have hExponent := small_of_tight (exponent_tight model) hL
  have hLedger : Small (ledger (model := model)) logarithm := below_ledger_small _ (fun _ => le_rfl)
  have hPrice := bound_small hL (GeneralPaperCompleteStoredPipelineWork.price_rate model hFast K) hLedger
  have hK := small_constant K (logarithm (model := model)) hL
  have hCap : Small (cap model K) logarithm := by
    unfold cap
    fun_prop
  have hBits := polylog_bits _ logarithm hL hCap
  unfold profile
  fun_prop

end Blotto.GeneralPaperPreparationCallerControls
