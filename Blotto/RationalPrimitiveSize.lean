import Blotto.BinaryWordWidth

/-! Canonical reduction cannot enlarge the numerator or a positive supplied
denominator. These bounds are the basis for local arithmetic size ledgers. -/

namespace Blotto

theorem reduced_fraction_bounds (a : ℤ) (d : ℕ) (hd : 0 < d) :
    ((a : ℚ) / d).num.natAbs ≤ a.natAbs ∧ ((a : ℚ) / d).den ≤ d := by
  have hdI : (d : ℤ) ≠ 0 := by exact_mod_cast ne_of_gt hd
  rcases Rat.exists_eq_mul_div_num_and_eq_mul_div_den a hdI with ⟨c, hn, hden⟩
  simp only [Int.cast_natCast] at hn hden
  have hp : (0 : ℤ) < ((a : ℚ) / d).den := by exact_mod_cast ((a : ℚ) / d).den_pos
  have hdi : (0 : ℤ) < d := by exact_mod_cast hd
  have hc : 0 < c := by nlinarith
  have hc1 : 1 ≤ c := by omega
  have hN : ((a : ℚ) / d).num.natAbs ≤ a.natAbs := by
    have he := congrArg Int.natAbs hn
    rw [Int.natAbs_mul] at he
    have hcN : 0 < c.natAbs := Int.natAbs_pos.mpr (ne_of_gt hc)
    have hcN1 : 1 ≤ c.natAbs := by omega
    calc
      _ = 1 * ((a : ℚ) / d).num.natAbs := by simp
      _ ≤ c.natAbs * ((a : ℚ) / d).num.natAbs := Nat.mul_le_mul_right _ hcN1
      _ = _ := he.symm

  have hD : (((a : ℚ) / d).den : ℤ) ≤ (d : ℤ) := by nlinarith
  exact ⟨hN, by exact_mod_cast hD⟩

end Blotto
