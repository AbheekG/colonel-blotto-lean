import Blotto.SparseMWPotential
import Blotto.BinaryWidthPrecision

/-! Exact rational floor-log-two scale selection uses numerator/denominator
binary lengths and one comparison. No search over a numerical exponent or
expanded score-power update is introduced. -/

namespace Blotto
namespace SparseMW

def scaleCandidate (x : ℚ) : ℤ := (x.num.toNat.log2 : ℤ) - (x.den.log2 : ℤ)

def candidateScale (x : ℚ) : ℚ := (2 : ℚ) ^ scaleCandidate x

def binaryScale (x : ℚ) : ℚ :=
  let candidate := candidateScale x
  if candidate ≤ x then candidate else candidate / 2

theorem candidateScale_positive (x : ℚ) : 0 < candidateScale x := by unfold candidateScale; positivity

theorem candidateScale_formula (x : ℚ) :
    candidateScale x = (2 : ℚ) ^ x.num.toNat.log2 / (2 : ℚ) ^ x.den.log2 := by
  unfold candidateScale scaleCandidate
  rw [zpow_sub₀ (by norm_num), zpow_natCast, zpow_natCast]

theorem candidateScale_range (x : ℚ) (hx : 0 < x) : candidateScale x / 2 < x ∧ x < 2 * candidateScale x := by
  have hn : 0 < x.num.toNat := Int.pos_iff_toNat_pos.mp (Rat.num_pos.mpr hx)
  have hd := x.den_pos
  have hNLow : 2 ^ x.num.toNat.log2 ≤ x.num.toNat := (Nat.le_log2 (ne_of_gt hn)).mp (le_refl _)
  have hNHigh := Nat.lt_log2_self (n := x.num.toNat)
  have hDLow : 2 ^ x.den.log2 ≤ x.den := (Nat.le_log2 (ne_of_gt hd)).mp (le_refl _)
  have hDHigh := Nat.lt_log2_self (n := x.den)
  have hNL : (2 : ℚ) ^ x.num.toNat.log2 ≤ (x.num.toNat : ℚ) := by exact_mod_cast hNLow
  have hNH : (x.num.toNat : ℚ) < (2 : ℚ) ^ (x.num.toNat.log2 + 1) := by exact_mod_cast hNHigh
  have hDL : (2 : ℚ) ^ x.den.log2 ≤ (x.den : ℚ) := by exact_mod_cast hDLow
  have hDH : (x.den : ℚ) < (2 : ℚ) ^ (x.den.log2 + 1) := by exact_mod_cast hDHigh
  have hNum : (x.num.toNat : ℚ) = (x.num : ℚ) := ProbabilityWords.nonnegative_numerator_cast x hx.le
  have hValue : x = (x.num.toNat : ℚ) / x.den := by rw [hNum, x.num_div_den]
  have hDp : (0 : ℚ) < x.den := by exact_mod_cast hd
  have hPN : (0 : ℚ) < 2 ^ x.num.toNat.log2 := by positivity
  have hPD : (0 : ℚ) < 2 ^ x.den.log2 := by positivity
  rw [pow_succ] at hNH hDH
  have hRatios :
      ((2 : ℚ) ^ x.num.toNat.log2 / 2 ^ x.den.log2) / 2 < (x.num.toNat : ℚ) / x.den ∧
      (x.num.toNat : ℚ) / x.den < 2 * ((2 : ℚ) ^ x.num.toNat.log2 / 2 ^ x.den.log2) := by
    constructor
    · have hCross : (2 : ℚ) ^ x.num.toNat.log2 * x.den <
          (x.num.toNat : ℚ) * (2 * 2 ^ x.den.log2) := by
        calc
          _ < (2 : ℚ) ^ x.num.toNat.log2 * (2 * 2 ^ x.den.log2) :=
            mul_lt_mul_of_pos_left (by simpa only [mul_comm] using hDH) hPN
          _ ≤ _ := mul_le_mul_of_nonneg_right hNL (by positivity)
      have he := (div_lt_div_iff₀ (mul_pos (by norm_num : (0 : ℚ) < 2) hPD) hDp).mpr hCross
      convert he using 1
      ring
    · have hCross : (x.num.toNat : ℚ) * 2 ^ x.den.log2 <
          (2 * (2 : ℚ) ^ x.num.toNat.log2) * x.den := by
        calc
          _ < (2 * (2 : ℚ) ^ x.num.toNat.log2) * 2 ^ x.den.log2 :=
            mul_lt_mul_of_pos_right (by simpa only [mul_comm] using hNH) hPD
          _ ≤ _ := mul_le_mul_of_nonneg_left hDL (by positivity)
      have he := (div_lt_div_iff₀ hDp hPD).mpr hCross
      convert he using 1
      ring
  rw [candidateScale_formula]
  constructor
  · exact hRatios.1.trans_eq hValue.symm
  · exact hValue.trans_lt hRatios.2

theorem binaryScale_bounds (x : ℚ) (hx : 0 < x) :
    0 < binaryScale x ∧ binaryScale x ≤ x ∧ x < 2 * binaryScale x := by
  have hc := candidateScale_positive x
  have hr := candidateScale_range x hx
  unfold binaryScale
  dsimp only
  split
  · rename_i hle
    exact ⟨hc, hle, hr.2⟩
  · rename_i hgt
    refine ⟨by positivity, hr.1.le, ?_⟩
    have he : 2 * (candidateScale x / 2) = candidateScale x := by ring
    rw [he]
    exact lt_of_not_ge hgt

end SparseMW
end Blotto
