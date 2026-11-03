import Blotto.GeneralPaperFirstAllBitDispatch

/-! Corrected complete equal preparation time includes the actual outer
branch test. The rate is on original input lengths, with one accuracy pass. -/
namespace Blotto.GeneralPaperFirstEqualDispatchTime
open GeneralPaperEqualInputDomain GeneralPaperUniformResourceGrowth
open GeneralPaperEqualUniformRateAlgebra
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

def price (model : RationalCostModel) (K : ℕ) (p : Input model) : ℕ :=
  GeneralPaperFirstStoredWork.price model K p+GeneralPaperMeasuredEqualDispatchFrame.branchPrice model p

theorem branch_rate (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) :
    Bound (GeneralPaperMeasuredEqualDispatchFrame.branchPrice model) ledger logarithm := by
  have hL : ∀ p : Input model,1≤logarithm p := logarithm_positive
  have hr : ∀ p : Input model,1≤ledger p := GeneralPaperEqualInputDomain.ledger_positive
  unfold GeneralPaperMeasuredEqualDispatchFrame.branchPrice
  fun_prop

theorem price_rate (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) (K : ℕ) :
    Bound (price model K) ledger logarithm :=
  bound_add _ _ ledger logarithm logarithm_positive
    (GeneralPaperFirstStoredWork.price_rate model hFast K) (branch_rate model hFast)

theorem paper_time (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) (K : ℕ) (hK : 1≤K) :
    ∃ C d : ℕ,∀ p : GeneralPaperOriginalGameInput.Input,p.n≠1 → p.budget=1 →
      (GeneralPaperFirstAllBitDispatch.run model K p).2 ≤
        C*GeneralPaperEqualInputHeadline.inputSize (GeneralPaperOriginalGameInput.equalInput model p)*
          (GeneralPaperEqualInputHeadline.paperLog (GeneralPaperOriginalGameInput.equalInput model p))^d := by
  obtain ⟨C,d,hBound⟩ := GeneralPaperEqualInputHeadline.transfer_rate (price_rate model hFast K)
  refine ⟨C,d,fun p hN hB => ?_⟩
  let ep := GeneralPaperOriginalGameInput.equalInput model p
  have hPrep := GeneralPaperFirstStoredWork.actual_work model K ep (Nat.mul_le_mul hK (logarithm_positive ep))
  rw [GeneralPaperFirstAllBitDispatch.on_equal model K p hN hB]
  change (GeneralPaperFirstMeasuredEqualPreparation.run model 1 K p).2+_ ≤ _
  rw [GeneralPaperFirstMeasuredEqualPreparation.work]
  exact (Nat.add_le_add_right hPrep _).trans (hBound ep)

end Blotto.GeneralPaperFirstEqualDispatchTime
