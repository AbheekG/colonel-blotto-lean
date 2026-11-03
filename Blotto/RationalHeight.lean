import Blotto.RationalPrimitiveSize

/-! Uniform bit-height bounds for reduced rationals and primitive operations.
Canonical reduction, signs and zero inversion are covered explicitly. -/

namespace Blotto

def RationalHeight (q : ℚ) (s : ℕ) : Prop := q.num.natAbs < 2 ^ s ∧ q.den < 2 ^ s

namespace RationalHeight

theorem positive {q : ℚ} {s : ℕ} (h : RationalHeight q s) : 0 < s := by
  by_contra hn
  have hs : s = 0 := by omega
  have hd := q.den_pos
  simp only [RationalHeight, hs, pow_zero] at h
  omega

theorem mono {q : ℚ} {s t : ℕ} (h : RationalHeight q s) (hst : s ≤ t) : RationalHeight q t :=
  ⟨h.1.trans_le (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hst),
    h.2.trans_le (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hst)⟩

theorem fraction (a : ℤ) (d s : ℕ) (hd : 0 < d) (ha : a.natAbs < 2 ^ s) (hden : d < 2 ^ s) :
    RationalHeight ((a : ℚ) / d) s :=
  ⟨(reduced_fraction_bounds a d hd).1.trans_lt ha, (reduced_fraction_bounds a d hd).2.trans_lt hden⟩

theorem mul {q r : ℚ} {s t : ℕ} (hq : RationalHeight q s) (hr : RationalHeight r t) :
    RationalHeight (q * r) (s + t) := by
  have he : ((q.num * r.num : ℤ) : ℚ) / (q.den * r.den : ℕ) = q * r := by
    push_cast
    rw [← div_mul_div_comm, q.num_div_den, r.num_div_den]
  rw [← he]
  apply fraction _ _ _ (Nat.mul_pos q.den_pos r.den_pos)
  · rw [Int.natAbs_mul, pow_add]
    exact (Nat.mul_le_mul_left q.num.natAbs (Nat.le_of_lt hr.1)).trans_lt
      (Nat.mul_lt_mul_of_pos_right hq.1 (Nat.two_pow_pos t))
  · rw [pow_add]
    exact (Nat.mul_le_mul_left q.den (Nat.le_of_lt hr.2)).trans_lt
      (Nat.mul_lt_mul_of_pos_right hq.2 (Nat.two_pow_pos t))

theorem neg {q : ℚ} {s : ℕ} (h : RationalHeight q s) : RationalHeight (-q) s := by
  simpa only [RationalHeight, Rat.num_neg_eq_neg_num, Rat.den_neg_eq_den, Int.natAbs_neg] using h

theorem inv {q : ℚ} {s : ℕ} (h : RationalHeight q s) : RationalHeight q⁻¹ s := by
  by_cases hz : q = 0
  · simpa only [hz, inv_zero] using h
  · have hn : q.num ≠ 0 := by
      intro hn
      have he := q.num_div_den
      rw [hn, Int.cast_zero, zero_div] at he
      exact hz he.symm
    have hs := Int.natAbs_sign_of_ne_zero hn
    simpa only [RationalHeight, Rat.num_inv, Rat.den_inv, ite_eq_right hn,
      Int.natAbs_mul, hs, Int.natAbs_natCast, one_mul] using And.intro h.2 h.1

theorem div {q r : ℚ} {s t : ℕ} (hq : RationalHeight q s) (hr : RationalHeight r t) :
    RationalHeight (q / r) (s + t) := by
  rw [div_eq_mul_inv]
  exact hq.mul hr.inv

theorem min {q r : ℚ} {s : ℕ} (hq : RationalHeight q s) (hr : RationalHeight r s) : RationalHeight (min q r) s := by
  by_cases h : q ≤ r
  · rw [min_eq_left h]; exact hq
  · rw [min_eq_right (le_of_lt (lt_of_not_ge h))]; exact hr

theorem max {q r : ℚ} {s : ℕ} (hq : RationalHeight q s) (hr : RationalHeight r s) : RationalHeight (max q r) s := by
  by_cases h : q ≤ r
  · rw [max_eq_right h]; exact hr
  · rw [max_eq_left (le_of_lt (lt_of_not_ge h))]; exact hq

end RationalHeight
end Blotto
