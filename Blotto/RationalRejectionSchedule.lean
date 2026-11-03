import Blotto.RejectionDyadicTail
import Blotto.RationalAccuracyPrecision

/-! Executable dyadic schedule: a ceiling factor block repeated E+1 times,
then enough precision for the total trial/node multiplicity. This is polynomial
in a supplied factor bound and E, not automatically in the raw input size. -/

namespace Blotto
open scoped BigOperators

def rationalFactorCeiling (factor : ℚ) : ℕ := (factor.num.toNat + factor.den - 1) / factor.den

theorem rationalFactorCeiling_bound (factor : ℚ) (hf : 0 ≤ factor) :
    factor ≤ (rationalFactorCeiling factor : ℚ) := by
  have hn : (factor.num.toNat : ℚ) = (factor.num : ℚ) := ProbabilityWords.nonnegative_numerator_cast factor hf
  have hd : 0 < factor.den := factor.den_pos
  have hNat : ∀ a d : ℕ, 0 < d → a ≤ ((a + d - 1) / d) * d := by
    intro a d hDen
    have he := Nat.div_add_mod (a + d - 1) d
    have hm := Nat.mod_lt (a + d - 1) hDen
    have he' : ((a + d - 1) / d) * d + (a + d - 1) % d = a + d - 1 := by
      simpa only [Nat.mul_comm] using he
    omega
  have hdiv : factor.num.toNat ≤ rationalFactorCeiling factor * factor.den :=
    hNat _ _ hd
  have hq : (factor.num.toNat : ℚ) ≤ (rationalFactorCeiling factor : ℚ) * factor.den := by exact_mod_cast hdiv
  rw [hn] at hq
  calc
    factor = (factor.num : ℚ) / factor.den := factor.num_div_den.symm
    _ ≤ (rationalFactorCeiling factor : ℚ) :=
      (div_le_iff₀ (by exact_mod_cast hd : (0 : ℚ) < factor.den)).mpr hq

def rejectionScheduleAttempts (factor : ℚ) (E : ℕ) : ℕ := rationalFactorCeiling factor * (E + 1)

def rejectionSchedulePrecision (nodes attempts E : ℕ) : ℕ := E + 1 + binaryWordWidth (attempts * (nodes + 1))

theorem rejectionSchedule_bit_error (nodes attempts E : ℕ) :
    (attempts : ℝ) * (((nodes : ℝ) + 1) * (1 / (2 : ℝ) ^ rejectionSchedulePrecision nodes attempts E)) ≤
      1 / (2 : ℝ) ^ (E + 1) := by
  have hWidth := lt_pow_binaryWordWidth (attempts * (nodes + 1))
  have hScale : (attempts : ℝ) * ((nodes : ℝ) + 1) ≤ (2 : ℝ) ^ binaryWordWidth (attempts * (nodes + 1)) := by
    exact_mod_cast Nat.le_of_lt hWidth
  have hPower : (0 : ℝ) < 2 ^ binaryWordWidth (attempts * (nodes + 1)) := by positivity
  have hE : (0 : ℝ) < 2 ^ (E + 1) := by positivity
  unfold rejectionSchedulePrecision
  rw [pow_add]
  have hBound := (div_le_one hPower).mpr hScale
  have he : (attempts : ℝ) * (((nodes : ℝ) + 1) * (1 / ((2 : ℝ) ^ (E + 1) * 2 ^ binaryWordWidth (attempts * (nodes + 1))))) =
      ((attempts : ℝ) * ((nodes : ℝ) + 1) / 2 ^ binaryWordWidth (attempts * (nodes + 1))) / 2 ^ (E + 1) := by ring
  rw [he]
  exact div_le_div_of_nonneg_right hBound hE.le

theorem rejectionSchedule_total_error (factor : ℚ) (hf : 1 ≤ factor) (nodes E : ℕ) :
    let attempts := rejectionScheduleAttempts factor E
    let K := rejectionSchedulePrecision nodes attempts E
    (attempts : ℝ) * (((nodes : ℝ) + 1) * (1 / (2 : ℝ) ^ K)) +
      (1 - 1 / (factor : ℝ)) ^ attempts ≤ 1 / (2 : ℝ) ^ E := by
  dsimp only
  have hg : (1 : ℝ) ≤ (factor : ℝ) := by exact_mod_cast hf
  have hblock : (factor : ℝ) ≤ (rationalFactorCeiling factor : ℝ) := by
    exact_mod_cast rationalFactorCeiling_bound factor (by linarith)
  have hTail := geometric_factor_blocks hg (rationalFactorCeiling factor) (E + 1) hblock
  have hBits := rejectionSchedule_bit_error nodes (rejectionScheduleAttempts factor E) E
  have hSum := add_le_add hBits hTail
  have he : (1 : ℝ) / 2 ^ (E + 1) + 1 / 2 ^ (E + 1) = 1 / 2 ^ E := by
    rw [pow_succ]
    field_simp
    ring
  exact hSum.trans_eq he

end Blotto
