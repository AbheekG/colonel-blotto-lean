import Blotto.RationalSignificandRounding

/-! A positive rational tolerance selects significant-bit precision by a
binary-width ratio comparison. The concrete rounder inherits the requested
relative error and the exponential certificate used by the sparse update. -/

namespace Blotto
namespace SparseMW

def roundingPrecision (theta : ℚ) : ℕ := binaryRatioPrecision theta.den theta.num.toNat

theorem roundingPrecision_guard (theta : ℚ) (ht : 0 < theta) :
    1 / (2 : ℚ) ^ roundingPrecision theta ≤ theta := by
  have hn : 0 < theta.num.toNat := Int.pos_iff_toNat_pos.mp (Rat.num_pos.mpr ht)
  have hd : (0 : ℚ) < theta.den := by exact_mod_cast theta.den_pos
  have heN := binaryRatioPrecision_bound theta.den theta.num.toNat hn
  have he : (theta.den : ℚ) ≤ (theta.num.toNat : ℚ) * (2 : ℚ) ^ roundingPrecision theta := by exact_mod_cast heN
  have hnum : (theta.num.toNat : ℚ) = theta * theta.den := by
    rw [ProbabilityWords.nonnegative_numerator_cast theta ht.le]
    exact (div_eq_iff (ne_of_gt hd)).mp theta.num_div_den
  rw [hnum] at he
  have hPower : (0 : ℚ) < (2 : ℚ) ^ roundingPrecision theta := by positivity
  apply (div_le_iff₀ hPower).mpr
  have he' : (1 : ℚ) ≤ theta * (2 : ℚ) ^ roundingPrecision theta := by
    apply (mul_le_mul_iff_of_pos_right hd).mp
    convert he using 1 <;> ring
  exact he'

def roundToTolerance (x theta : ℚ) : ℚ := roundDown x (roundingPrecision theta)

theorem roundToTolerance_certificate (x theta : ℚ) (hx : 0 < x) (ht : 0 < theta) :
    0 < roundToTolerance x theta ∧ roundToTolerance x theta ≤ x ∧
      x < (1 + theta) * roundToTolerance x theta := by
  have hr := roundDown_certificate x hx (roundingPrecision theta)
  have hp := roundingPrecision_guard theta ht
  refine ⟨hr.1, hr.2.1, ?_⟩
  exact hr.2.2.trans_le (mul_le_mul_of_nonneg_right (by linarith) hr.1.le)

theorem roundToTolerance_exp_lower (x theta : ℚ) (hx : 0 < x) (ht : 0 < theta) :
    Real.exp (-(theta : ℝ)) * (x : ℝ) ≤ (roundToTolerance x theta : ℝ) := by
  have hr := roundToTolerance_certificate x theta hx ht
  have he : (x : ℝ) ≤ (1 + (theta : ℝ)) * (roundToTolerance x theta : ℝ) := by exact_mod_cast hr.2.2.le
  have hPos : (0 : ℝ) ≤ (roundToTolerance x theta : ℝ) := by exact_mod_cast hr.1.le
  have hexp : 1 + (theta : ℝ) ≤ Real.exp (theta : ℝ) := by simpa only [add_comm] using Real.add_one_le_exp (theta : ℝ)
  have hProduct := he.trans (mul_le_mul_of_nonneg_right hexp hPos)
  have hMul := mul_le_mul_of_nonneg_left hProduct (Real.exp_pos (-(theta : ℝ))).le
  have hCancel : Real.exp (-(theta : ℝ)) * Real.exp (theta : ℝ) = 1 := by rw [← Real.exp_add]; simp
  simpa only [← mul_assoc, hCancel, one_mul] using hMul

end SparseMW
end Blotto
