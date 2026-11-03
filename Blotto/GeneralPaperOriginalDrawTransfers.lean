import Blotto.GeneralPaperOriginalDrawParameters

/-! The actual draw majorants transfer to one original-input headline.
Equal draws retain expected work; unequal and one-field work remain bounded
for every supplied fresh-bit string or deterministic output, respectively. -/
namespace Blotto.GeneralPaperOriginalDrawTransfers
open GeneralPaperOriginalGameInput GeneralPaperOriginalDrawParameters
open scoped ENNReal
set_option autoImplicit false
set_option maxHeartbeats 6500000
set_option maxRecDepth 16384

theorem raise (p : Input) (cost A B e f : ℕ) (hA : A ≤ B) (he : e ≤ f)
    (h : (cost : ℚ) ≤ (A : ℚ) * drawScale p * (logarithm p : ℚ) ^ e) :
    (cost : ℚ) ≤ (B : ℚ) * drawScale p * (logarithm p : ℚ) ^ f := by
  have hS : 0 ≤ drawScale p := (by norm_num : (0 : ℚ) ≤ 1).trans (scale_positive p)
  have hL : (logarithm p : ℚ) ^ e ≤ (logarithm p : ℚ) ^ f := by
    exact_mod_cast Nat.pow_le_pow_right (lt_of_lt_of_le (by decide : 0 < (1 : ℕ)) (log_positive p)) he
  exact h.trans (mul_le_mul (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hA) hS) hL (by positivity) (by positivity))

theorem equal_bound (model : RationalCostModel) (A e cost : ℕ) (p : Input)
    (h : cost ≤ A * GeneralPaperStoredSelectedReturnWork.inputScale (equalInput model p) *
      GeneralPaperStoredNativeReadRates.drawLog (equalInput model p) ^ e) :
    (cost : ℚ) ≤ ((A * 4 * 4 ^ e : ℕ) : ℚ) * drawScale p * (logarithm p : ℚ) ^ (e + 1) := by
  have hb := (h.trans (Nat.mul_le_mul (Nat.mul_le_mul_left A (equal_scale model p))
    (Nat.pow_le_pow_left (equal_log model p) e)))
  have hn : cost ≤ (A * 4 * 4 ^ e) * baseScale p * logarithm p ^ (e + 1) :=
    hb.trans_eq (by rw [mul_pow, pow_succ]; ring)
  have hQ : (cost : ℚ) ≤ ((A * 4 * 4 ^ e : ℕ) : ℚ) * (baseScale p : ℚ) * (logarithm p : ℚ) ^ (e + 1) := by
    exact_mod_cast hn
  exact hQ.trans (by gcongr; exact base_le_scale p)

theorem equal_rate (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) (K : ℕ) :
    ∃ A e : ℕ, ∀ p : Input, (GeneralPaperStoredPipelineDrawWork.majorant model 1 K (equalInput model p) : ℚ) ≤
      (A : ℚ) * drawScale p * (logarithm p : ℚ) ^ e := by
  obtain ⟨A, e, h⟩ := GeneralPaperStoredPipelineDrawWork.rate model hFast 1 K
  exact ⟨A * 4 * 4 ^ e, e + 1, fun p => equal_bound model A e _ p (h (equalInput model p))⟩

theorem native_bound (p : Input) (hStrict : p.budget < 1) (A e cost : ℕ)
    (h : (cost : ℚ) ≤ (A : ℚ) * GeneralPaperNativeDrawHeadline.drawScale (unequalInput p hStrict) *
      (GeneralPaperNativeDrawHeadline.drawLog (unequalInput p hStrict) : ℚ) ^ e) :
    (cost : ℚ) ≤ (A : ℚ) * drawScale p * (logarithm p : ℚ) ^ e := by
  have hL : (GeneralPaperNativeDrawHeadline.drawLog (unequalInput p hStrict) : ℚ) ≤ logarithm p := by
    exact_mod_cast native_log p hStrict
  have hP : (GeneralPaperNativeDrawHeadline.drawLog (unequalInput p hStrict) : ℚ) ^ e ≤ (logarithm p : ℚ) ^ e := by
    gcongr
  have hS : 0 ≤ drawScale p := (by norm_num : (0 : ℚ) ≤ 1).trans (scale_positive p)
  exact h.trans (mul_le_mul (mul_le_mul_of_nonneg_left (native_scale p hStrict) (Nat.cast_nonneg A)) hP (by positivity) (by positivity))

theorem one_bound (p : Input) (poor : Bool) : (GeneralPaperOneFieldBitOutput.run p poor).work ≤
    512 * baseScale p := by
  have h := GeneralPaperOneFieldBitOutput.input_linear p poor
  have hn := fields_positive p
  have hi : originalSize p ≤ baseScale p := by unfold baseScale; nlinarith only [hn]
  exact h.trans (Nat.mul_le_mul_left 512 hi)

theorem one_rate (p : Input) (poor : Bool) : ((GeneralPaperOneFieldBitOutput.run p poor).work : ℚ) ≤
    512 * drawScale p * (logarithm p : ℚ) ^ 0 := by
  have h : ((GeneralPaperOneFieldBitOutput.run p poor).work : ℚ) ≤ 512 * (baseScale p : ℚ) := by
    exact_mod_cast one_bound p poor
  simpa only [pow_zero, mul_one] using h.trans (mul_le_mul_of_nonneg_left (base_le_scale p) (by norm_num : (0 : ℚ) ≤ 512))

theorem ennreal_bound (cost : ℕ) (bound : ℚ) (h : (cost : ℚ) ≤ bound) :
    (cost : ℝ≥0∞) ≤ ENNReal.ofReal (bound : ℝ) := by
  have hR : (cost : ℝ) ≤ (bound : ℝ) := by exact_mod_cast h
  simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal hR

end Blotto.GeneralPaperOriginalDrawTransfers
