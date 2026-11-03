import Blotto.RationalHeight

/-! Addition/subtraction increase the sum of operand bit heights by at most
one bit. No positivity or separation of the operands is assumed. -/

namespace Blotto.RationalHeight

theorem add {q r : ℚ} {s t : ℕ} (hq : RationalHeight q s) (hr : RationalHeight r t) :
    RationalHeight (q + r) (s + t + 1) := by
  let a : ℤ := q.num * r.den + r.num * q.den
  let d : ℕ := q.den * r.den
  have hqrep : (q.num : ℚ) = q * (q.den : ℚ) :=
    (div_eq_iff (by exact_mod_cast q.den_ne_zero)).mp q.num_div_den
  have hrrep : (r.num : ℚ) = r * (r.den : ℚ) :=
    (div_eq_iff (by exact_mod_cast r.den_ne_zero)).mp r.num_div_den
  have he : (a : ℚ) / d = q + r := by
    dsimp only [a, d]
    push_cast
    rw [hqrep, hrrep]
    have hdq : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_ne_zero
    have hdr : (r.den : ℚ) ≠ 0 := by exact_mod_cast r.den_ne_zero
    field_simp
  have hterm1 : q.num.natAbs * r.den < 2 ^ (s + t) := by
    rw [pow_add]
    exact (Nat.mul_le_mul_left q.num.natAbs (Nat.le_of_lt hr.2)).trans_lt
      (Nat.mul_lt_mul_of_pos_right hq.1 (Nat.two_pow_pos t))
  have hterm2 : r.num.natAbs * q.den < 2 ^ (s + t) := by
    rw [Nat.add_comm s t, pow_add]
    exact (Nat.mul_le_mul_left r.num.natAbs (Nat.le_of_lt hq.2)).trans_lt
      (Nat.mul_lt_mul_of_pos_right hr.1 (Nat.two_pow_pos s))
  have ha : a.natAbs < 2 ^ (s + t + 1) := by
    have hn := Int.natAbs_add_le (q.num * r.den) (r.num * q.den)
    simp only [Int.natAbs_mul, Int.natAbs_natCast] at hn
    change (q.num * r.den + r.num * q.den).natAbs < 2 ^ (s + t + 1)
    rw [pow_succ]
    omega
  have hd : d < 2 ^ (s + t + 1) := by
    have hprod : q.den * r.den < 2 ^ (s + t) := by
      rw [pow_add]
      exact (Nat.mul_le_mul_left q.den (Nat.le_of_lt hr.2)).trans_lt
        (Nat.mul_lt_mul_of_pos_right hq.2 (Nat.two_pow_pos t))
    exact hprod.trans_le (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega))
  rw [← he]
  exact fraction a d _ (Nat.mul_pos q.den_pos r.den_pos) ha hd

theorem sub {q r : ℚ} {s t : ℕ} (hq : RationalHeight q s) (hr : RationalHeight r t) :
    RationalHeight (q - r) (s + t + 1) := by
  rw [sub_eq_add_neg]
  exact hq.add hr.neg

end Blotto.RationalHeight
