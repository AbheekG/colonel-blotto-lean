import Blotto.BinaryAccuracyWords
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! The actual ratio selector differs by at most five bits from the paper's
ceiling logarithm. Raw positive numerator/denominator words need no reduction.
These mathematical bridges do not execute a real logarithm. -/

namespace Blotto

theorem binaryRatioPrecision_scale32_bounds (a b : ℕ) (hb : 0 < b) :
    binaryRatioPrecision a b ≤ binaryRatioPrecision (32*a) b ∧
      binaryRatioPrecision (32*a) b ≤ binaryRatioPrecision a b+5 := by
  constructor
  · apply binaryRatioPrecision_minimal a b hb
    have h := binaryRatioPrecision_bound (32*a) b hb
    nlinarith
  · apply binaryRatioPrecision_minimal (32*a) b hb
    have h := Nat.mul_le_mul_left 32 (binaryRatioPrecision_bound a b hb)
    simpa only [pow_add, show (2:ℕ)^5=32 by decide, Nat.mul_assoc,
      Nat.mul_comm, Nat.mul_left_comm] using h

namespace BinaryAccuracyInput

def logExponent (a : BinaryAccuracyInput) : ℕ := binaryRatioPrecision a.denominator a.numerator

theorem logExponent_guard (a : BinaryAccuracyInput) :
    1 ≤ a.real*(2:ℝ)^a.logExponent := by
  have hn := binaryRatioPrecision_bound a.denominator a.numerator a.numerator_pos
  have hr : (a.denominator:ℝ) ≤ (a.numerator:ℝ)*(2:ℝ)^a.logExponent := by exact_mod_cast hn
  have hd : (0:ℝ)<a.denominator := by exact_mod_cast a.denominator_pos
  apply (mul_le_mul_iff_of_pos_right hd).mp
  unfold real
  convert! hr using 1 <;> field_simp

theorem logExponent_minimal (a : BinaryAccuracyInput) (t : ℕ)
    (ht : 1 ≤ a.real*(2:ℝ)^t) : a.logExponent ≤ t := by
  have hd : (0:ℝ)<a.denominator := by exact_mod_cast a.denominator_pos
  have hr := mul_le_mul_of_nonneg_right ht (le_of_lt hd)
  have hreal : (a.denominator:ℝ) ≤ (a.numerator:ℝ)*(2:ℝ)^t := by
    unfold real at hr
    convert! hr using 1 <;> field_simp
  have hn : a.denominator ≤ a.numerator*2^t := by exact_mod_cast hreal
  exact binaryRatioPrecision_minimal a.denominator a.numerator a.numerator_pos t hn

theorem logExponent_eq_ceil (a : BinaryAccuracyInput) :
    a.logExponent = ⌈Real.logb 2 (1/a.real)⌉₊ := by
  have hx : 0 < 1/a.real := one_div_pos.mpr a.real_pos
  apply Nat.le_antisymm
  · apply a.logExponent_minimal
    have hc : Real.logb 2 (1/a.real) ≤ (⌈Real.logb 2 (1/a.real)⌉₊:ℝ) := Nat.le_ceil _
    have hp := (Real.logb_le_iff_le_rpow (by norm_num : (1:ℝ)<2) hx).mp hc
    rw [Real.rpow_natCast, div_le_iff₀ a.real_pos] at hp
    simpa only [mul_comm] using hp
  · rw [Nat.ceil_le, Real.logb_le_iff_le_rpow (by norm_num : (1:ℝ)<2) hx,
      Real.rpow_natCast, div_le_iff₀ a.real_pos]
    simpa only [mul_comm] using a.logExponent_guard

theorem precision_log_bounds (a : BinaryAccuracyInput) :
    a.logExponent ≤ a.precision ∧ a.precision ≤ a.logExponent+5 :=
  binaryRatioPrecision_scale32_bounds a.denominator a.numerator a.numerator_pos

theorem sampleBitBudget_log_bound (a : BinaryAccuracyInput) (n : ℕ) :
    RationalLottoResourceSystem.sampleBitBudget n a.precision ≤
      3*n+5*a.logExponent+3025 := by
  have h := a.precision_log_bounds
  rw [RationalLottoResourceSystem.sampleBitBudget_eq]
  omega

theorem sampleBitBudget_ceil_bound (a : BinaryAccuracyInput) (n : ℕ) :
    RationalLottoResourceSystem.sampleBitBudget n a.precision ≤
      3*n+5*⌈Real.logb 2 (1/a.real)⌉₊+3025 := by
  rw [← a.logExponent_eq_ceil]
  exact a.sampleBitBudget_log_bound n

def ofPositiveRational (ε : ℚ) (hε : 0 < ε) : BinaryAccuracyInput :=
  ⟨ε.num.toNat, ε.den, Int.pos_iff_toNat_pos.mp (Rat.num_pos.mpr hε), ε.den_pos⟩

theorem ofPositiveRational_precision (ε : ℚ) (hε : 0 < ε) :
    (ofPositiveRational ε hε).precision = rationalAccuracyPrecision ε := rfl

theorem ofPositiveRational_real (ε : ℚ) (hε : 0 < ε) :
    (ofPositiveRational ε hε).real = (ε:ℝ) := by
  have hq : (ε.num.toNat:ℚ)/(ε.den:ℚ) = ε := by
    rw [ProbabilityWords.nonnegative_numerator_cast ε (le_of_lt hε), ε.num_div_den]
  change (ε.num.toNat:ℝ)/(ε.den:ℝ) = (ε:ℝ)
  simpa only [Rat.cast_div, Rat.cast_natCast] using congrArg (fun q:ℚ => (q:ℝ)) hq

end BinaryAccuracyInput

theorem rationalAccuracyPrecision_log_bounds (ε : ℚ) (hε : 0 < ε) :
    ⌈Real.logb 2 (1/(ε:ℝ))⌉₊ ≤ rationalAccuracyPrecision ε ∧
      rationalAccuracyPrecision ε ≤ ⌈Real.logb 2 (1/(ε:ℝ))⌉₊+5 := by
  have h := (BinaryAccuracyInput.ofPositiveRational ε hε).precision_log_bounds
  rw [BinaryAccuracyInput.logExponent_eq_ceil, BinaryAccuracyInput.ofPositiveRational_real,
    BinaryAccuracyInput.ofPositiveRational_precision] at h
  exact h

theorem rationalPRG_sampleBitBudget_log_bound (ε : ℚ) (hε : 0 < ε) (n : ℕ) :
    RationalLottoResourceSystem.sampleBitBudget n (rationalAccuracyPrecision ε) ≤
      3*n+5*⌈Real.logb 2 (1/(ε:ℝ))⌉₊+3025 := by
  have h := rationalAccuracyPrecision_log_bounds ε hε
  rw [RationalLottoResourceSystem.sampleBitBudget_eq]
  omega

theorem BinaryAccuracyWords.sampleBitBudget_log_bound (a : BinaryAccuracyWords) (n : ℕ) :
    RationalLottoResourceSystem.sampleBitBudget n a.precision ≤
      3*n+5*⌈Real.logb 2 (1/a.numeric.real)⌉₊+3025 := by
  rw [a.precision_eq]
  exact a.numeric.sampleBitBudget_ceil_bound n

end Blotto
