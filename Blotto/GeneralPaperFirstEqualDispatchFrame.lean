import Blotto.GeneralPaperFirstStoredProgramContract
import Blotto.GeneralPaperMeasuredEqualDispatchFrame

/-! Saved fields of the outer original-input equal dispatcher. The branch
test, actual prepared-source/complete work and returned tag coexist. -/
namespace Blotto.GeneralPaperFirstEqualDispatchFrame
open GeneralPaperEqualInputDomain GeneralPaperUniformResourceGrowth
open GeneralPaperEncodedScalarStorage (fields natBits)
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 16384

def branchPrice (model : RationalCostModel) (p : Input model) : ℕ :=
  model.rat (rationalWordWidth p.budget + 3) + 64 * (binaryWordWidth p.n + 1)

def values (model : RationalCostModel) (K : ℕ) (p : Input model) : List ℕ :=
  [K, p.n, p.k, word K p, 1, (GeneralPaperEqualFirstInputPipeline.run model 1 K p).1.address,
    (GeneralPaperEqualFirstInputPipeline.run model 1 K p).2, (GeneralPaperFirstStoredPipeline.run model 1 K p).2,
    branchPrice model p, (GeneralPaperFirstStoredPipeline.run model 1 K p).2 + branchPrice model p]

def cap (model : RationalCostModel) (K : ℕ) (p : Input model) : ℕ :=
  GeneralPaperFirstStoredCaller.cap model K p + branchPrice model p + 1

def window (model : RationalCostModel) (K : ℕ) (p : Input model) : ℕ :=
  fields (word K p) (values model K p) + 128 * word K p

def profile (model : RationalCostModel) (K : ℕ) (p : Input model) : ℕ :=
  10 * (natBits (cap model K p) + word K p) + 160 * word K p

theorem values_bound (model : RationalCostModel) (K : ℕ) (p : Input model) (hK : 1 ≤ K) :
    ∀ z ∈ values model K p, z ≤ cap model K p := by
  have hW : 1 ≤ word K p := Nat.mul_le_mul hK (logarithm_positive p)
  have hp := GeneralPaperFirstStoredWork.actual_work model K p hW
  have hShape := GeneralPaperFirstStoredWork.work_identity model 1 K p
  intro z hz
  simp only [values, List.mem_cons, List.not_mem_nil, or_false] at hz
  unfold cap GeneralPaperFirstStoredCaller.cap
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
  obtain ⟨C,hC⟩ := GeneralPaperFirstStoredCapacity.envelope_small model hFast
  have hEnvelope : Small (GeneralPaperFirstStoredCapacity.envelope model K) logarithm := by
    refine ⟨C*(binaryWordWidth K+2), fun p => ?_⟩
    have h := hC ⟨p,1,K⟩
    change binaryWordWidth (GeneralPaperFirstStoredCapacity.envelope model K p) ≤
      C*(logarithm p+binaryWordWidth 1+binaryWordWidth K) at h
    have hl := hL p
    norm_num only [show binaryWordWidth 1=1 by decide] at h
    have hm : logarithm p+1+binaryWordWidth K ≤ (binaryWordWidth K+2)*logarithm p := by
      nlinarith only [Nat.mul_le_mul_left (binaryWordWidth K+1) hl]
    exact h.trans ((Nat.mul_le_mul_left C hm).trans_eq (by ring))
  have hCap : Small (GeneralPaperFirstStoredCaller.cap model K) logarithm :=
    small_mono hEnvelope (fun p => by unfold GeneralPaperFirstStoredCapacity.envelope; omega)
  have hBranch := branch_small model hFast
  unfold cap
  fun_prop

theorem profile_polylog (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) (K : ℕ) :
    Polylog (profile model K) logarithm := by
  have hL : ∀ p : Input model, 1 ≤ logarithm p := logarithm_positive
  have hBits := polylog_bits _ _ hL (cap_small model hFast K)
  have hWord := polylog_of_tight (word_tight K model)
  unfold profile
  fun_prop

end Blotto.GeneralPaperFirstEqualDispatchFrame
