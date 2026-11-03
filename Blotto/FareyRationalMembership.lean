import Blotto.FareyRankRepresentation

/-! Native canonical rational membership and reflection for direct Farey cut
inversion. A rational value belongs to the bounded-denominator set exactly when
its stored reduced denominator passes the order guard. No enumeration or
membership oracle is introduced. -/

namespace Blotto.Farey

def fractionOfRat (x : ℚ) : Fraction := ⟨x.num.toNat, x.den, x.den_pos⟩
def complement (x : Fraction) : Fraction := ⟨x.den - x.num, x.den, x.den_pos⟩

theorem fractionOfRat_value (x : ℚ) (h : 0 ≤ x) : (fractionOfRat x).value = x := by
  unfold fractionOfRat Fraction.value
  rw [ProbabilityWords.nonnegative_numerator_cast x h]
  exact x.num_div_den

theorem value_den_dvd (x : Fraction) : x.value.den ∣ x.den := by
  have h := Rat.den_dvd (x.num : ℤ) (x.den : ℤ)
  have he : Rat.divInt (x.num : ℤ) (x.den : ℤ) = x.value := by
    rw [Rat.divInt_eq_div]
    push_cast
    rfl
  rw [he] at h
  exact_mod_cast h

theorem value_den_le (x : Fraction) : x.value.den ≤ x.den := Nat.le_of_dvd x.den_pos (value_den_dvd x)

theorem rational_member_iff (D : ℕ) (x : ℚ) (h : 0 ≤ x) :
    x.den ≤ D ↔ ∃ represented : Fraction, represented.den ≤ D ∧ represented.value = x := by
  constructor
  · intro hd
    exact ⟨fractionOfRat x, hd, fractionOfRat_value x h⟩
  · rintro ⟨represented, hd, he⟩
    rw [← he]
    exact (value_den_le represented).trans hd

theorem num_le_den (x : Fraction) (h : x.value ≤ 1) : x.num ≤ x.den := by
  have hd : (0 : ℚ) < x.den := by exact_mod_cast x.den_pos
  have hn := (div_le_one hd).mp h
  exact_mod_cast hn

theorem complement_value (x : Fraction) (h : x.value ≤ 1) : (complement x).value = 1 - x.value := by
  have hn := num_le_den x h
  have hd : (x.den : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt x.den_pos
  unfold complement Fraction.value
  rw [Nat.cast_sub hn]
  field_simp

theorem complement_unit (x : Fraction) (h : x.value ≤ 1) : (complement x).value ≤ 1 := by
  rw [complement_value x h]
  linarith [value_nonnegative x]

theorem reflected_den_bound (D : ℕ) (x : ℚ) (h : 0 ≤ x ∧ x ≤ 1) (hd : x.den ≤ D) : (1 - x).den ≤ D := by
  have hf := fractionOfRat_value x h.1
  have hu : (fractionOfRat x).value ≤ 1 := by rw [hf]; exact h.2
  have he := complement_value (fractionOfRat x) hu
  rw [hf] at he
  rw [← he]
  exact (value_den_le (complement (fractionOfRat x))).trans hd

theorem reflected_member_iff (D : ℕ) (x : ℚ) (h : 0 ≤ x ∧ x ≤ 1) :
    (1 - x).den ≤ D ↔ x.den ≤ D := by
  constructor
  · intro hd
    have he := reflected_den_bound D (1 - x) (by constructor <;> linarith) hd
    have hx : 1 - (1 - x) = x := by ring
    rwa [hx] at he
  · exact reflected_den_bound D x h

end Blotto.Farey
