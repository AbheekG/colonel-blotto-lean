import Blotto.SparseMWComputedMultiplier

/-! The actual sparse stored update rounds the accumulated weight product,
not just its exponential multiplier. Its old-weight-dependent ratio has the
effective-loss guarantee needed by the fixed-significand R136/R143 source. -/

namespace Blotto
namespace SparseMW

def storedUpdate (old eta loss theta : ℚ) : ℚ :=
  roundToTolerance (old * expMultiplierNative (eta * loss) theta) theta

def storedRatio (old eta loss theta : ℚ) : ℚ := storedUpdate old eta loss theta / old

theorem storedUpdate_positive (old eta loss theta : ℚ) (hOld : 0 < old)
    (hx : 0 ≤ eta * loss ∧ eta * loss ≤ 1 / 4) (ht : 0 < theta ∧ theta ≤ 1 / 2) :
    0 < storedUpdate old eta loss theta :=
  (roundToTolerance_certificate _ theta
    (mul_pos hOld (expMultiplierNative_unit _ _ hx ht).1) ht.1).1

theorem storedUpdate_decreases (old eta loss theta : ℚ) (hOld : 0 < old)
    (hx : 0 ≤ eta * loss ∧ eta * loss ≤ 1 / 4) (ht : 0 < theta ∧ theta ≤ 1 / 2) :
    storedUpdate old eta loss theta ≤ old := by
  have hc := expMultiplierNative_unit _ _ hx ht
  have hr := roundToTolerance_certificate (old * expMultiplierNative (eta * loss) theta) theta
    (mul_pos hOld hc.1) ht.1
  exact hr.2.1.trans (mul_le_of_le_one_right hOld.le hc.2)

theorem storedRatio_positive (old eta loss theta : ℚ) (hOld : 0 < old)
    (hx : 0 ≤ eta * loss ∧ eta * loss ≤ 1 / 4) (ht : 0 < theta ∧ theta ≤ 1 / 2) :
    0 < storedRatio old eta loss theta :=
  div_pos (storedUpdate_positive old eta loss theta hOld hx ht) hOld

theorem storedRatio_unit (old eta loss theta : ℚ) (hOld : 0 < old)
    (hx : 0 ≤ eta * loss ∧ eta * loss ≤ 1 / 4) (ht : 0 < theta ∧ theta ≤ 1 / 2) :
    0 < storedRatio old eta loss theta ∧ storedRatio old eta loss theta ≤ 1 :=
  ⟨storedRatio_positive old eta loss theta hOld hx ht,
    (div_le_one hOld).mpr (storedUpdate_decreases old eta loss theta hOld hx ht)⟩

theorem storedUpdate_exact_ratio (old eta loss theta : ℚ) (hOld : old ≠ 0) :
    old * storedRatio old eta loss theta = storedUpdate old eta loss theta := by
  unfold storedRatio
  field_simp

theorem storedRatio_certificate (old eta loss theta : ℚ) (hOld : 0 < old)
    (hx : 0 ≤ eta * loss ∧ eta * loss ≤ 1 / 4) (ht : 0 < theta ∧ theta ≤ 1 / 2) :
    Real.exp (-(eta : ℝ) * (loss : ℝ) - 3 * (theta : ℝ)) ≤ (storedRatio old eta loss theta : ℝ) ∧
      (storedRatio old eta loss theta : ℝ) ≤ Real.exp (-(eta : ℝ) * (loss : ℝ)) := by
  have hc := expMultiplierNative_certificate (eta * loss) theta hx ht
  have hProduct : 0 < old * expMultiplierNative (eta * loss) theta := mul_pos hOld hc.1
  have hr := roundToTolerance_certificate (old * expMultiplierNative (eta * loss) theta) theta hProduct ht.1
  have hround := roundToTolerance_exp_lower (old * expMultiplierNative (eta * loss) theta) theta hProduct ht.1
  have hOldR : (0 : ℝ) < (old : ℝ) := by exact_mod_cast hOld
  have hlower : Real.exp (-(eta : ℝ) * (loss : ℝ) - 3 * (theta : ℝ)) * (old : ℝ) ≤
      (storedUpdate old eta loss theta : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left hc.2.1
      (mul_nonneg (Real.exp_pos (-(theta : ℝ))).le hOldR.le)
    have he : Real.exp (-(theta : ℝ)) * (old : ℝ) *
        Real.exp (-((eta * loss : ℚ) : ℝ) - 2 * (theta : ℝ)) =
        Real.exp (-(eta : ℝ) * (loss : ℝ) - 3 * (theta : ℝ)) * (old : ℝ) := by
      rw [Rat.cast_mul]
      simp only [neg_mul]
      rw [mul_right_comm, ← Real.exp_add]
      congr 2
      ring
    rw [he] at hmul
    have hr' : Real.exp (-(theta : ℝ)) * ((old : ℝ) * (expMultiplierNative (eta * loss) theta : ℝ)) ≤
        (storedUpdate old eta loss theta : ℝ) := by simpa only [storedUpdate, Rat.cast_mul] using hround
    exact hmul.trans (by simpa only [mul_assoc] using hr')
  have hupper : (storedUpdate old eta loss theta : ℝ) ≤
      (old : ℝ) * Real.exp (-(eta : ℝ) * (loss : ℝ)) := by
    have hrR : (storedUpdate old eta loss theta : ℝ) ≤
        (old : ℝ) * (expMultiplierNative (eta * loss) theta : ℝ) := by exact_mod_cast hr.2.1
    have hcR : (expMultiplierNative (eta * loss) theta : ℝ) ≤ Real.exp (-(eta : ℝ) * (loss : ℝ)) := by
      simpa only [Rat.cast_mul, neg_mul] using hc.2.2
    exact hrR.trans (mul_le_mul_of_nonneg_left hcR hOldR.le)
  constructor
  · unfold storedRatio
    rw [Rat.cast_div]
    exact (le_div_iff₀ hOldR).mpr hlower
  · unfold storedRatio
    rw [Rat.cast_div]
    exact (div_le_iff₀ hOldR).mpr (by simpa only [mul_comm] using hupper)

theorem storedRatio_effectiveLoss (old eta loss theta : ℚ) (hOld : 0 < old) (heta : 0 < eta)
    (hx : 0 ≤ eta * loss ∧ eta * loss ≤ 1 / 4) (ht : 0 < theta ∧ theta ≤ 1 / 2) :
    (loss : ℝ) ≤ effectiveLoss (eta : ℝ) (storedRatio old eta loss theta : ℝ) ∧
      effectiveLoss (eta : ℝ) (storedRatio old eta loss theta : ℝ) ≤
        (loss : ℝ) + 3 * (theta : ℝ) / (eta : ℝ) := by
  have he := storedRatio_certificate old eta loss theta hOld hx ht
  exact effectiveLoss_error (by exact_mod_cast heta) he.1 he.2

theorem storedUpdate_mantissa (old eta loss theta : ℚ) :
    storedUpdate old eta loss theta =
      (roundMantissa (old * expMultiplierNative (eta * loss) theta) (roundingPrecision theta) : ℚ) *
        (2 : ℚ) ^ (selectedExponent (old * expMultiplierNative (eta * loss) theta) - roundingPrecision theta) :=
  roundDown_mantissa _ _

theorem storedUpdate_mantissa_width (old eta loss theta : ℚ) (hOld : 0 < old)
    (hx : 0 ≤ eta * loss ∧ eta * loss ≤ 1 / 4) (ht : 0 < theta ∧ theta ≤ 1 / 2) :
    binaryWordWidth (roundMantissa (old * expMultiplierNative (eta * loss) theta) (roundingPrecision theta)).toNat ≤
      roundingPrecision theta + 1 :=
  roundMantissa_wordWidth _ (mul_pos hOld (expMultiplierNative_unit _ _ hx ht).1) _

theorem storedUpdate_exponent_size (old eta loss theta : ℚ) :
    (selectedExponent (old * expMultiplierNative (eta * loss) theta) - roundingPrecision theta).natAbs ≤
      binaryWordWidth (old * expMultiplierNative (eta * loss) theta).num.toNat +
        binaryWordWidth (old * expMultiplierNative (eta * loss) theta).den + 1 + roundingPrecision theta := by
  have he := selectedExponent_abs (old * expMultiplierNative (eta * loss) theta)
  have hs := Int.natAbs_sub_le (selectedExponent (old * expMultiplierNative (eta * loss) theta))
    (roundingPrecision theta : ℤ)
  simp only [Int.natAbs_natCast] at hs
  omega

end SparseMW
end Blotto
