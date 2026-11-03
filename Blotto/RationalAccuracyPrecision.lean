import Blotto.ProbabilityWords
import Blotto.BinaryRatioPrecision

/-! A native precision selector implements the least power of two sufficient
for 32/ε, using bit lengths and one shift comparison, without full division.
Positive rational accuracy is an explicit input certificate. -/

namespace Blotto

def rationalAccuracyPrecision (ε : ℚ) : ℕ :=
  binaryRatioPrecision (32 * ε.den) ε.num.toNat

theorem rationalAccuracyPrecision_numerator_bound (ε : ℚ) (hε : 0 < ε) :
    32 * ε.den ≤ 2 ^ rationalAccuracyPrecision ε * ε.num.toNat := by
  have hn : 0 < ε.num.toNat := Int.pos_iff_toNat_pos.mp (Rat.num_pos.mpr hε)
  simpa only [rationalAccuracyPrecision, mul_comm] using binaryRatioPrecision_bound (32 * ε.den) ε.num.toNat hn

theorem rationalAccuracyPrecision_guard (ε : ℚ) (hε : 0 < ε) :
    32 ≤ ε * (2 : ℚ) ^ rationalAccuracyPrecision ε := by
  have hd : (0 : ℚ) < ε.den := by exact_mod_cast ε.den_pos
  have hn : (ε.num.toNat : ℚ) = ε * ε.den := by
    rw [ProbabilityWords.nonnegative_numerator_cast ε (le_of_lt hε)]
    exact (div_eq_iff (ne_of_gt hd)).mp ε.num_div_den
  have hQ : (32 : ℚ) * ε.den ≤ (2 : ℚ) ^ rationalAccuracyPrecision ε * (ε.num.toNat : ℚ) := by
    exact_mod_cast rationalAccuracyPrecision_numerator_bound ε hε
  rw [hn] at hQ
  apply (mul_le_mul_iff_of_pos_right hd).mp
  convert! hQ using 1; ring

theorem rationalAccuracyPrecision_minimal (ε : ℚ) (hε : 0 < ε) (K : ℕ)
    (hK : 32 ≤ ε * (2 : ℚ) ^ K) : rationalAccuracyPrecision ε ≤ K := by
  have hn : 0 < ε.num.toNat := Int.pos_iff_toNat_pos.mp (Rat.num_pos.mpr hε)
  have hd : (0 : ℚ) < ε.den := by exact_mod_cast ε.den_pos
  have hnum : (ε.num.toNat : ℚ) = ε * ε.den := by
    rw [ProbabilityWords.nonnegative_numerator_cast ε (le_of_lt hε)]
    exact (div_eq_iff (ne_of_gt hd)).mp ε.num_div_den
  have hQ : (32 : ℚ) * ε.den ≤ (2 : ℚ) ^ K * (ε.num.toNat : ℚ) := by
    rw [hnum]
    convert! mul_le_mul_of_nonneg_right hK (le_of_lt hd) using 1; ring
  have hN : 32 * ε.den ≤ 2 ^ K * ε.num.toNat := by exact_mod_cast hQ
  exact binaryRatioPrecision_minimal (32 * ε.den) ε.num.toNat hn K (by simpa only [mul_comm] using hN)

theorem rationalAccuracyPrecision_real_guard (ε : ℚ) (hε : 0 < ε) :
    32 ≤ (ε : ℝ) * (2 : ℝ) ^ rationalAccuracyPrecision ε := by
  exact_mod_cast rationalAccuracyPrecision_guard ε hε

theorem rationalAccuracyPrecision_candidate_wordWidth (ε : ℚ) (hε : 0 < ε) (h32 : ε < 32) :
    binaryWordWidth (ε.num.toNat <<< ratioLogDifference (32 * ε.den) ε.num.toNat) ≤
      6 + binaryWordWidth ε.den := by
  have hn : 0 < ε.num.toNat := Int.pos_iff_toNat_pos.mp (Rat.num_pos.mpr hε)
  have hd : (0 : ℚ) < ε.den := by exact_mod_cast ε.den_pos
  have hc : (ε.num.toNat : ℚ) = (ε.num : ℚ) := ProbabilityWords.nonnegative_numerator_cast ε (le_of_lt hε)
  have hq : (ε.num.toNat : ℚ) < (32 : ℚ) * ε.den := by
    rw [hc]
    exact (div_lt_iff₀ hd).mp (by simpa only [ε.num_div_den] using h32)
  have hN : ε.num.toNat < 32 * ε.den := by exact_mod_cast hq
  have hw := ratio_shift_wordWidth (32 * ε.den) ε.num.toNat hn hN
  have hp := binaryWordWidth_mul 32 ε.den
  have he : binaryWordWidth 32 = 6 := by decide
  rw [he] at hp
  exact hw.trans hp

end Blotto
