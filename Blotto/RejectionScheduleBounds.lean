import Blotto.RationalScheduledRejection

/-! The constructed schedule has explicit numerical parameter bounds. A
polynomial bound in learner input still requires its proved factor/guide size
majorants; the schedule itself does not hide them. -/

namespace Blotto

theorem rationalFactorCeiling_le_successor (factor : ℚ) (hf : 0 ≤ factor) :
    (rationalFactorCeiling factor : ℚ) ≤ factor + 1 := by
  have hd := factor.den_pos
  have hNat : ∀ a d : ℕ, 0 < d → ((a + d - 1) / d) * d ≤ a + d := by
    intro a d hDen
    have he := Nat.div_mul_le_self (a + d - 1) d
    omega
  have hn := hNat factor.num.toNat factor.den hd
  have hq : (rationalFactorCeiling factor : ℚ) * factor.den ≤ (factor.num.toNat : ℚ) + factor.den := by
    exact_mod_cast hn
  rw [ProbabilityWords.nonnegative_numerator_cast factor hf] at hq
  have hDen : (0 : ℚ) < factor.den := by exact_mod_cast hd
  apply (mul_le_mul_iff_of_pos_right hDen).mp
  have hProduct : factor * factor.den = (factor.num : ℚ) :=
    ((div_eq_iff (ne_of_gt hDen)).mp factor.num_div_den).symm
  have he : (factor + 1) * factor.den = (factor.num : ℚ) + factor.den := by
    rw [add_mul, one_mul, hProduct]
  rw [he]
  exact hq

theorem rejectionScheduleAttempts_bound (factor : ℚ) (hf : 0 ≤ factor) (E : ℕ) :
    (rejectionScheduleAttempts factor E : ℚ) ≤ (factor + 1) * (E + 1) := by
  unfold rejectionScheduleAttempts
  rw [Nat.cast_mul]
  have hE : (0 : ℚ) ≤ ((E + 1 : ℕ) : ℚ) := by positivity
  simpa only [Nat.cast_add, Nat.cast_one] using mul_le_mul_of_nonneg_right (rationalFactorCeiling_le_successor factor hf) hE

theorem rejectionSchedulePrecision_bound (nodes attempts E : ℕ) :
    rejectionSchedulePrecision nodes attempts E ≤ E + 1 + binaryWordWidth attempts + binaryWordWidth (nodes + 1) := by
  have he := binaryWordWidth_mul attempts (nodes + 1)
  unfold rejectionSchedulePrecision
  omega

end Blotto
