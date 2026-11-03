import Blotto.PlayerSpecificRationalPrecision
import Blotto.PRGAccuracyLogarithm

/-! Computed scaled precisions equal the paper's ceiling logarithms.
These real logarithms occur only in the specification, never in code. -/
namespace Blotto.PlayerSpecificRationalPrecisionLog
open PlayerSpecificRationalPrecision
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem ceil_eq (C : ℕ) (epsilon : ℚ) (he : 0 < epsilon) (hC : 0 < C) :
    exponent C epsilon=⌈Real.logb 2 ((C:ℝ)/(epsilon:ℝ))⌉₊ := by
  have hr : (0:ℝ) < epsilon := by exact_mod_cast he
  have hc : (0:ℝ) < C := by exact_mod_cast hC
  have hx : 0 < (C:ℝ)/(epsilon:ℝ) := div_pos hc hr
  apply Nat.le_antisymm
  · apply real_minimal C epsilon he
    have hceil : Real.logb 2 ((C:ℝ)/(epsilon:ℝ)) ≤ (⌈Real.logb 2 ((C:ℝ)/(epsilon:ℝ))⌉₊:ℝ) := Nat.le_ceil _
    have hp := (Real.logb_le_iff_le_rpow (by norm_num : (1:ℝ) < 2) hx).mp hceil
    rw [Real.rpow_natCast,div_le_iff₀ hr] at hp
    simpa only [mul_comm] using hp
  · rw [Nat.ceil_le,Real.logb_le_iff_le_rpow (by norm_num : (1:ℝ) < 2) hx,
      Real.rpow_natCast,div_le_iff₀ hr]
    simpa only [mul_comm] using real_guard C epsilon he

theorem logarithmic_bound (C : ℕ) (epsilon : ℚ) (he : 0 < epsilon) :
    exponent C epsilon ≤ ⌈Real.logb 2 (1/(epsilon:ℝ))⌉₊+binaryWordWidth C := by
  have h := scale_bound C epsilon he
  have h1 := ceil_eq 1 epsilon he (by decide)
  simp only [Nat.cast_one] at h1
  rw [h1] at h
  exact h

end Blotto.PlayerSpecificRationalPrecisionLog
