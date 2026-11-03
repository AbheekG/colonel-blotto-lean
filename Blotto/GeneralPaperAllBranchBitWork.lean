import Blotto.GeneralPaperAllBranchBitOutput

/-! Work of the literal branch dispatcher: one selected producer executes
once, with explicit input branch-test prices. Global headline transfer and
single-pass executable calibration remain separate obligations. -/
namespace Blotto.GeneralPaperAllBranchBitWork
open GeneralPaperOriginalGameInput GeneralPaperAllBranchBitDispatch
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 16384

theorem one_work (model : RationalCostModel) (C d K : ℕ) (p : Input) (hN : p.n = 1) :
    (run model C d K p).2 ≤ 288 * (rationalWordWidth p.budget + 3) + 64 + 64 * (binaryWordWidth p.n + 1) := by
  rw [on_one model C d K p hN]
  have h := GeneralPaperOneFieldRealPreparation.work 1 p.budget
  exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.mul_le_mul_right _ h) 64) _

theorem branch_price {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d) (p : Input) :
    branchPrice model p ≤ GeneralPaperFastRationalModel.charge C d (rationalWordWidth p.budget + 3) +
      64 * (binaryWordWidth p.n + 1) :=
  Nat.add_le_add_right (hg _) _

theorem equal_work (model : RationalCostModel) (C d K : ℕ) (p : Input) (hN : p.n ≠ 1) (hB : p.budget = 1) :
    (run model C d K p).2 ≤ GeneralPaperCompleteStoredPipelineWork.price model K (equalInput model p) + branchPrice model p := by
  rw [on_equal model C d K p hN hB]
  exact Nat.add_le_add_right (GeneralPaperCompleteStoredPipelineWork.work model K (equalInput model p)) _

theorem unequal_work {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d)
    (K : ℕ) (p : Input) (hN : p.n ≠ 1) (hB : p.budget ≠ 1) :
    (run model C d K p).2 ≤ GeneralPaperNativePreparationTimeRates.bitPrice model C d (unequalInput p (strict_of_ne p hB)) +
      branchPrice model p := by
  rw [on_unequal model C d K p hN hB]
  exact Nat.add_le_add_right (GeneralPaperNativePreparationTimeRates.native_bit_work hg (unequalInput p (strict_of_ne p hB))) _

end Blotto.GeneralPaperAllBranchBitWork
