import Blotto.GeneralPaperFirstOriginalDrawParameters
import Blotto.GeneralPaperOriginalDrawTransfers

namespace Blotto.GeneralPaperFirstOriginalDrawTransfers
open GeneralPaperOriginalGameInput GeneralPaperOriginalDrawParameters
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

theorem equal_bound (model : RationalCostModel) (A e cost : ℕ) (p : Input)
    (h : cost ≤ A * GeneralPaperFirstStoredDrawRates.inputScale (equalInput model p) *
      GeneralPaperFirstStoredDrawRates.drawLog (equalInput model p) ^ e) :
    (cost : ℚ) ≤ ((A * 4 * 4 ^ e : ℕ) : ℚ) * drawScale p * (logarithm p : ℚ) ^ (e + 1) := by
  have hb := (h.trans (Nat.mul_le_mul (Nat.mul_le_mul_left A (GeneralPaperFirstOriginalDrawParameters.equal_scale model p))
    (Nat.pow_le_pow_left (GeneralPaperFirstOriginalDrawParameters.equal_log model p) e)))
  have hn : cost ≤ (A * 4 * 4 ^ e) * baseScale p * logarithm p ^ (e + 1) :=
    hb.trans_eq (by rw [mul_pow, pow_succ]; ring)
  have hQ : (cost : ℚ) ≤ ((A * 4 * 4 ^ e : ℕ) : ℚ) * (baseScale p : ℚ) * (logarithm p : ℚ) ^ (e + 1) := by
    exact_mod_cast hn
  exact hQ.trans (by gcongr; exact base_le_scale p)

theorem equal_rate (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) (K : ℕ) :
    ∃ A e : ℕ, ∀ p : Input, (GeneralPaperFirstStoredPipelineDrawWork.majorant model 1 K (equalInput model p) : ℚ) ≤
      (A : ℚ) * drawScale p * (logarithm p : ℚ) ^ e := by
  obtain ⟨A, e, h⟩ := GeneralPaperFirstStoredDrawRates.pipeline_rate model hFast 1 K
  exact ⟨A * 4 * 4 ^ e, e + 1, fun p => equal_bound model A e _ p (h (equalInput model p))⟩


end Blotto.GeneralPaperFirstOriginalDrawTransfers
