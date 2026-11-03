import Blotto.RationalPRGInput

/-! A fixed positive common denominator survives all resource-rounding
add/sub/min/max operations. The predicate concerns reduced stored rationals. -/

namespace Blotto
open scoped BigOperators

def OnRationalLattice (D : ℕ) (q : ℚ) : Prop := q.den ∣ D

namespace OnRationalLattice

theorem zero (D : ℕ) : OnRationalLattice D 0 := by simp [OnRationalLattice]

theorem intCast (D : ℕ) (a : ℤ) : OnRationalLattice D (a : ℚ) := by simp [OnRationalLattice]

theorem add {D : ℕ} {q r : ℚ} (hq : OnRationalLattice D q) (hr : OnRationalLattice D r) :
    OnRationalLattice D (q + r) := (Rat.add_den_dvd_lcm q r).trans (Nat.lcm_dvd hq hr)

theorem sub {D : ℕ} {q r : ℚ} (hq : OnRationalLattice D q) (hr : OnRationalLattice D r) :
    OnRationalLattice D (q - r) := (Rat.sub_den_dvd_lcm q r).trans (Nat.lcm_dvd hq hr)

theorem min {D : ℕ} {q r : ℚ} (hq : OnRationalLattice D q) (hr : OnRationalLattice D r) :
    OnRationalLattice D (min q r) := by
  by_cases h : q ≤ r
  · rw [min_eq_left h]; exact hq
  · rw [min_eq_right (le_of_lt (lt_of_not_ge h))]; exact hr

theorem max {D : ℕ} {q r : ℚ} (hq : OnRationalLattice D q) (hr : OnRationalLattice D r) :
    OnRationalLattice D (max q r) := by
  by_cases h : q ≤ r
  · rw [max_eq_right h]; exact hr
  · rw [max_eq_left (le_of_lt (lt_of_not_ge h))]; exact hq

theorem mul {D E : ℕ} {q r : ℚ} (hq : OnRationalLattice D q) (hr : OnRationalLattice E r) :
    OnRationalLattice (D * E) (q * r) := (Rat.mul_den_dvd q r).trans (Nat.mul_dvd_mul hq hr)

theorem int_mul {D : ℕ} {q : ℚ} (hq : OnRationalLattice D q) (a : ℤ) :
    OnRationalLattice D ((a : ℚ) * q) := by
  have he : ((a : ℚ) * q).den ∣ q.den := by
    simpa only [Rat.den_intCast, one_mul] using Rat.mul_den_dvd (a : ℚ) q
  exact he.trans hq

theorem enlarge {D E : ℕ} {q : ℚ} (hq : OnRationalLattice D q) (hDE : D ∣ E) : OnRationalLattice E q := hq.trans hDE

theorem list_sum {α : Type*} {D : ℕ} (f : α → ℚ) (xs : List α) (h : ∀ x ∈ xs, OnRationalLattice D (f x)) :
    OnRationalLattice D ((xs.map f).sum) := by
  induction xs with
  | nil => exact zero D
  | cons x xs ih =>
    exact add (h x (by simp)) (ih (fun y hy => h y (by simp [hy])))

theorem finset_sum {α : Type*} {D : ℕ} (f : α → ℚ) (s : Finset α) (h : ∀ x ∈ s, OnRationalLattice D (f x)) :
    OnRationalLattice D (∑ x ∈ s, f x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using zero D
  | @insert x s hx ih =>
    rw [Finset.sum_insert hx]
    exact add (h x (by simp)) (ih (fun y hy => h y (by simp [hy])))

end OnRationalLattice
end Blotto
