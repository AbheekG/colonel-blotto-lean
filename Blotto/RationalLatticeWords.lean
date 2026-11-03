import Blotto.RationalLattice

/-! Native integer words on a supplied common denominator. Decoding and
range bounds connect the integer representation to reduced rational storage. -/

namespace Blotto

def latticeNumerator (D : ℕ) (q : ℚ) : ℤ := q.num * (D / q.den : ℕ)

theorem latticeNumerator_cast_eq_mul {D : ℕ} {q : ℚ} (hq : OnRationalLattice D q) :
    (latticeNumerator D q : ℚ) = q * (D : ℚ) := by
  rcases hq with ⟨k, hk⟩
  have he : D / q.den = k := by rw [hk]; exact Nat.mul_div_cancel_left k q.den_pos
  have hd : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_ne_zero
  have hrep : (q.num : ℚ) = q * (q.den : ℚ) := (div_eq_iff hd).mp q.num_div_den
  rw [latticeNumerator, he]
  push_cast
  rw [hrep, hk, Nat.cast_mul]
  ring

theorem latticeNumerator_decode {D : ℕ} (hD : 0 < D) {q : ℚ} (hq : OnRationalLattice D q) :
    (latticeNumerator D q : ℚ) / D = q := by
  rw [latticeNumerator_cast_eq_mul hq]
  exact mul_div_cancel_right₀ q (by exact_mod_cast ne_of_gt hD)

theorem rationalLattice_den_le {D : ℕ} (hD : 0 < D) {q : ℚ} (hq : OnRationalLattice D q) : q.den ≤ D :=
  Nat.le_of_dvd hD hq

theorem latticeNumerator_bounds {D : ℕ} {q : ℚ} (hq : OnRationalLattice D q) (h : 0 ≤ q ∧ q ≤ 1) :
    0 ≤ latticeNumerator D q ∧ latticeNumerator D q ≤ (D : ℤ) := by
  have hd : (0 : ℚ) ≤ D := Nat.cast_nonneg D
  have he := latticeNumerator_cast_eq_mul hq
  have hb : (0 : ℚ) ≤ (latticeNumerator D q : ℚ) ∧ (latticeNumerator D q : ℚ) ≤ (D : ℚ) := by
    rw [he]
    exact ⟨mul_nonneg h.1 hd, by simpa only [one_mul] using mul_le_mul_of_nonneg_right h.2 hd⟩
  exact_mod_cast hb

theorem rationalLattice_reduced_numerator_le {D : ℕ} (hD : 0 < D) {q : ℚ}
    (hq : OnRationalLattice D q) (h : 0 ≤ q ∧ q ≤ 1) : q.num.toNat ≤ D := by
  have hd : (0 : ℚ) < q.den := by exact_mod_cast q.den_pos
  have he : (q.num : ℚ) ≤ q.den := by
    have hl := h.2
    rw [← q.num_div_den, div_le_one hd] at hl
    exact hl
  have hn : (q.num.toNat : ℚ) ≤ q.den := by
    rw [ProbabilityWords.nonnegative_numerator_cast q h.1]
    exact he
  have hN : q.num.toNat ≤ q.den := by exact_mod_cast hn
  exact hN.trans (rationalLattice_den_le hD hq)

theorem latticeNumerator_add {D : ℕ} {q r : ℚ} (hq : OnRationalLattice D q) (hr : OnRationalLattice D r) :
    latticeNumerator D (q + r) = latticeNumerator D q + latticeNumerator D r := by
  have h : ((latticeNumerator D (q + r) : ℤ) : ℚ) = ((latticeNumerator D q + latticeNumerator D r : ℤ) : ℚ) := by
    rw [latticeNumerator_cast_eq_mul (hq.add hr), Int.cast_add,
      latticeNumerator_cast_eq_mul hq, latticeNumerator_cast_eq_mul hr]
    ring
  exact_mod_cast h

theorem latticeNumerator_sub {D : ℕ} {q r : ℚ} (hq : OnRationalLattice D q) (hr : OnRationalLattice D r) :
    latticeNumerator D (q - r) = latticeNumerator D q - latticeNumerator D r := by
  have h : ((latticeNumerator D (q - r) : ℤ) : ℚ) = ((latticeNumerator D q - latticeNumerator D r : ℤ) : ℚ) := by
    rw [latticeNumerator_cast_eq_mul (hq.sub hr), Int.cast_sub,
      latticeNumerator_cast_eq_mul hq, latticeNumerator_cast_eq_mul hr]
    ring
  exact_mod_cast h

end Blotto
