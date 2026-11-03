import Blotto.GeneralPaperAllBranchRealCorrectness

/-! Common real-RAM scale for boundary and unequal branches. Its logarithm
contains only the field count and inverse accuracy, not input precision. -/
namespace Blotto.GeneralPaperAllBranchRealTimeAlgebra
open GeneralPaperOriginalRealInput
open GeneralPaperRealHeadlineParameters (timeScale logarithm)
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 16384

theorem scale_ge_fields (p : Input) : (p.n : ℚ) ≤ timeScale p.n p.epsilon := by
  have hE := p.epsilon_valid.1
  have h : 0 ≤ (GeneralPaperRealHeadlineParameters.nStar p.n p.epsilon) ^ 2 / p.epsilon ^ 5 := by positivity
  unfold timeScale
  linarith only [h]

theorem scale_positive (p : Input) : (1 : ℚ) ≤ timeScale p.n p.epsilon := by
  have hn : (1 : ℚ) ≤ p.n := by exact_mod_cast p.selector.fields_positive
  exact hn.trans (scale_ge_fields p)

theorem log_positive (p : Input) : (1 : ℚ) ≤ (logarithm p.n p.epsilon : ℚ) := by
  exact_mod_cast GeneralPaperRealHeadlineParameters.logarithm_positive p.n p.epsilon

theorem absorb_overhead (p : Input) (cost coefficient exponent overhead : ℕ)
    (h : (cost : ℚ) ≤ (coefficient : ℚ) * timeScale p.n p.epsilon * (logarithm p.n p.epsilon : ℚ) ^ exponent) :
    ((cost + overhead : ℕ) : ℚ) ≤ ((coefficient + overhead : ℕ) : ℚ) *
      timeScale p.n p.epsilon * (logarithm p.n p.epsilon : ℚ) ^ exponent := by
  have hr := scale_positive p
  have hp : (1 : ℚ) ≤ (logarithm p.n p.epsilon : ℚ) ^ exponent := by
    exact_mod_cast (Nat.one_le_pow _ _ (GeneralPaperRealHeadlineParameters.logarithm_positive p.n p.epsilon))
  have hu : (1 : ℚ) ≤ timeScale p.n p.epsilon * (logarithm p.n p.epsilon : ℚ) ^ exponent := by
    have hm := mul_le_mul hr hp (by norm_num : (0 : ℚ) ≤ 1) ((by norm_num : (0 : ℚ) ≤ 1).trans hr)
    simpa using hm
  have ho := mul_le_mul_of_nonneg_left hu (Nat.cast_nonneg (α := ℚ) overhead)
  push_cast
  nlinarith only [h, ho]

theorem raise_bound (p : Input) (cost a b i j : ℕ) (hab : a ≤ b) (hij : i ≤ j)
    (h : (cost : ℚ) ≤ (a : ℚ) * timeScale p.n p.epsilon * (logarithm p.n p.epsilon : ℚ) ^ i) :
    (cost : ℚ) ≤ (b : ℚ) * timeScale p.n p.epsilon * (logarithm p.n p.epsilon : ℚ) ^ j := by
  have hr : 0 ≤ timeScale p.n p.epsilon := (by norm_num : (0 : ℚ) ≤ 1).trans (scale_positive p)
  have hp : (logarithm p.n p.epsilon : ℚ) ^ i ≤ (logarithm p.n p.epsilon : ℚ) ^ j := by
    exact_mod_cast Nat.pow_le_pow_right
      (show 0 < logarithm p.n p.epsilon from lt_of_lt_of_le (by decide) (GeneralPaperRealHeadlineParameters.logarithm_positive p.n p.epsilon)) hij
  exact h.trans (mul_le_mul (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hab) hr) hp (by positivity) (by positivity))

end Blotto.GeneralPaperAllBranchRealTimeAlgebra
