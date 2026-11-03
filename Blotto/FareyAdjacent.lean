import Blotto.MonotoneResourceCuts

/-! Exact bounded-denominator facts used by the retained quotient Farey
predecessor and R127 rank encoding. Fractions are labelled numerator/denominator
pairs; no finite sequence or code universe is enumerated. -/

namespace Blotto.Farey

structure Fraction where
  num : ℕ
  den : ℕ
  den_pos : 0 < den

def Fraction.value (x : Fraction) : ℚ := (x.num : ℚ) / x.den

def Adjacent (left right : Fraction) : Prop :=
  right.num * left.den = left.num * right.den + 1

def mediant (left right : Fraction) : Fraction :=
  ⟨left.num + right.num, left.den + right.den, by have hp := left.den_pos; omega⟩

theorem value_nonnegative (x : Fraction) : 0 ≤ x.value := by
  unfold Fraction.value
  positivity

theorem value_lt_iff (left right : Fraction) :
    left.value < right.value ↔ left.num * right.den < right.num * left.den := by
  have hl : (0 : ℚ) < left.den := by exact_mod_cast left.den_pos
  have hr : (0 : ℚ) < right.den := by exact_mod_cast right.den_pos
  unfold Fraction.value
  rw [div_lt_div_iff₀ hl hr]
  exact_mod_cast Iff.rfl

theorem value_le_iff (left right : Fraction) :
    left.value ≤ right.value ↔ left.num * right.den ≤ right.num * left.den := by
  have hl : (0 : ℚ) < left.den := by exact_mod_cast left.den_pos
  have hr : (0 : ℚ) < right.den := by exact_mod_cast right.den_pos
  unfold Fraction.value
  rw [div_le_div_iff₀ hl hr]
  exact_mod_cast Iff.rfl

theorem adjacent_lt {left right : Fraction} (h : Adjacent left right) : left.value < right.value := by
  apply (value_lt_iff left right).mpr
  unfold Adjacent at h
  omega

theorem adjacent_mediant_left {left right : Fraction} (h : Adjacent left right) :
    Adjacent left (mediant left right) := by
  unfold Adjacent mediant at *
  dsimp
  nlinarith

theorem adjacent_mediant_right {left right : Fraction} (h : Adjacent left right) :
    Adjacent (mediant left right) right := by
  unfold Adjacent mediant at *
  dsimp
  nlinarith

theorem mediant_between {left right : Fraction} (h : Adjacent left right) :
    left.value < (mediant left right).value ∧ (mediant left right).value < right.value :=
  ⟨adjacent_lt (adjacent_mediant_left h), adjacent_lt (adjacent_mediant_right h)⟩

theorem denominator_between {left right middle : Fraction} (h : Adjacent left right)
    (hl : left.value < middle.value) (hr : middle.value < right.value) :
    left.den + right.den ≤ middle.den := by
  have hlc := Nat.succ_le_of_lt ((value_lt_iff left middle).mp hl)
  have hrc := Nat.succ_le_of_lt ((value_lt_iff middle right).mp hr)
  have h1 := Nat.mul_le_mul_left right.den hlc
  have h2 := Nat.mul_le_mul_left left.den hrc
  have hd := congrArg (fun z : ℕ => z * middle.den) h
  unfold Adjacent at h
  nlinarith

theorem no_bounded_between {left right : Fraction} (D : ℕ) (h : Adjacent left right)
    (hD : D < left.den + right.den) (middle : Fraction) (hm : middle.den ≤ D) :
    ¬ (left.value < middle.value ∧ middle.value < right.value) := by
  intro hi
  have hb := denominator_between h hi.1 hi.2
  omega

theorem left_greatest_below {left right : Fraction} (D : ℕ) (h : Adjacent left right)
    (hD : D < left.den + right.den) (cutoff : ℚ) (hc : cutoff ≤ right.value)
    (middle : Fraction) (hm : middle.den ≤ D) (hBelow : middle.value < cutoff) :
    middle.value ≤ left.value := by
  by_contra hg
  have hl : left.value < middle.value := lt_of_not_ge hg
  exact no_bounded_between D h hD middle hm ⟨hl, hBelow.trans_le hc⟩

theorem separation {left right : Fraction} (h : left.value < right.value) :
    1 / ((left.den : ℚ) * right.den) ≤ right.value - left.value := by
  have hc := Nat.succ_le_of_lt ((value_lt_iff left right).mp h)
  have hcq : (left.num : ℚ) * right.den + 1 ≤ (right.num : ℚ) * left.den := by exact_mod_cast hc
  have hl : (0 : ℚ) < left.den := by exact_mod_cast left.den_pos
  have hr : (0 : ℚ) < right.den := by exact_mod_cast right.den_pos
  unfold Fraction.value
  apply (div_le_iff₀ (mul_pos hl hr)).mpr
  field_simp
  nlinarith

theorem bounded_separation (D : ℕ) {left right : Fraction}
    (hl : left.den ≤ D) (hr : right.den ≤ D) (h : left.value < right.value) :
    1 / ((D : ℚ) * D) ≤ right.value - left.value := by
  have hD : 0 < D := left.den_pos.trans_le hl
  have hprod : (left.den : ℚ) * right.den ≤ (D : ℚ) * D := by
    exact_mod_cast Nat.mul_le_mul hl hr
  have hp : (0 : ℚ) < (left.den : ℚ) * right.den := by
    exact_mod_cast Nat.mul_pos left.den_pos right.den_pos
  exact (one_div_le_one_div_of_le hp hprod).trans (separation h)

def rankScale (D : ℕ) : ℕ := 4 * D * D
def rankCap (D : ℕ) : ℕ := 2 * rankScale D
def closedCode (D : ℕ) (x : Fraction) : ℕ := 2 * Nat.floor ((rankScale D : ℚ) * x.value)

theorem scaled_separation (D : ℕ) {left right : Fraction}
    (hl : left.den ≤ D) (hr : right.den ≤ D) (h : left.value < right.value) :
    (rankScale D : ℚ) * left.value + 4 ≤ (rankScale D : ℚ) * right.value := by
  have hD : (0 : ℚ) < D := by exact_mod_cast left.den_pos.trans_le hl
  have hs := bounded_separation D hl hr h
  have he := mul_le_mul_of_nonneg_left hs (by positivity : (0 : ℚ) ≤ (rankScale D : ℚ))
  unfold rankScale at he ⊢
  push_cast at he ⊢
  have hx : (4 * (D : ℚ) * D) * (1 / ((D : ℚ) * D)) = 4 := by field_simp
  rw [hx] at he
  nlinarith

theorem floor_separation (D : ℕ) {left right : Fraction}
    (hl : left.den ≤ D) (hr : right.den ≤ D) (h : left.value < right.value) :
    Nat.floor ((rankScale D : ℚ) * left.value) + 4 ≤ Nat.floor ((rankScale D : ℚ) * right.value) := by
  have hn : (0 : ℚ) ≤ (rankScale D : ℚ) * left.value := mul_nonneg (by positivity) (value_nonnegative left)
  have hf := Nat.floor_mono (scaled_separation D hl hr h)
  change Nat.floor ((rankScale D : ℚ) * left.value + ((4 : ℕ) : ℚ)) ≤ _ at hf
  rw [Nat.floor_add_natCast hn 4] at hf
  exact hf

theorem closedCode_separation (D : ℕ) {left right : Fraction}
    (hl : left.den ≤ D) (hr : right.den ≤ D) (h : left.value < right.value) :
    closedCode D left + 8 ≤ closedCode D right := by
  have hf := floor_separation D hl hr h
  unfold closedCode
  omega

end Blotto.Farey
