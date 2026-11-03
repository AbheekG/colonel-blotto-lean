import Blotto.FareyAdjacent

/-! The actual quotient jumps of the retained Stern--Brocot bracket routine.
All jumps use exact rational floors and integer denominator quotients. The
terminal extension supplies the strict predecessor when a cutoff is itself a
Farey member; it is the same adjacent-fraction characterization used by the
retained modular-inverse implementation. No fractions are enumerated. -/

namespace Blotto.Farey

def leftJump (left right : Fraction) (k : ℕ) : Fraction :=
  ⟨left.num + k * right.num, left.den + k * right.den, by have hp := left.den_pos; omega⟩

def rightJump (left right : Fraction) (k : ℕ) : Fraction :=
  ⟨right.num + k * left.num, right.den + k * left.den, by have hp := right.den_pos; omega⟩

def denominatorJump (D : ℕ) (first second : Fraction) : ℕ := (D - first.den) / second.den

def terminalPredecessor (D : ℕ) (left right : Fraction) : Fraction :=
  leftJump left right (denominatorJump D left right)

def leftRatio (left right : Fraction) (cutoff : ℚ) : ℚ :=
  (cutoff * left.den - left.num) / (right.num - cutoff * right.den)

def rightRatio (left right : Fraction) (cutoff : ℚ) : ℚ :=
  (right.num - cutoff * right.den) / (cutoff * left.den - left.num)

def leftQuotient (D : ℕ) (left right : Fraction) (cutoff : ℚ) : ℕ :=
  min (Nat.floor (leftRatio left right cutoff)) (denominatorJump D left right)

def rightQuotient (D : ℕ) (left right : Fraction) (cutoff : ℚ) : ℕ :=
  min (Nat.floor (rightRatio left right cutoff)) (denominatorJump D right left)

theorem leftJump_adjacent {left right : Fraction} (h : Adjacent left right) (k : ℕ) :
    Adjacent (leftJump left right k) right := by
  unfold Adjacent leftJump at *
  dsimp
  nlinarith

theorem rightJump_adjacent {left right : Fraction} (h : Adjacent left right) (k : ℕ) :
    Adjacent left (rightJump left right k) := by
  unfold Adjacent rightJump at *
  dsimp
  nlinarith

theorem consecutive_leftJump {left right : Fraction} (h : Adjacent left right) (k : ℕ) :
    Adjacent (leftJump left right k) (leftJump left right (k + 1)) := by
  unfold Adjacent leftJump at *
  dsimp
  nlinarith

theorem denominatorJump_bounds (D : ℕ) (first second : Fraction) (hD : first.den ≤ D) :
    (leftJump first second (denominatorJump D first second)).den ≤ D ∧
      D < (leftJump first second (denominatorJump D first second)).den + second.den := by
  have hm := Nat.mod_lt (D - first.den) second.den_pos
  have he := Nat.mod_add_div (D - first.den) second.den
  unfold leftJump denominatorJump
  dsimp
  rw [Nat.mul_comm second.den] at he
  omega

theorem leftJump_den_bound (D : ℕ) (left right : Fraction) (hD : left.den ≤ D) (k : ℕ)
    (hk : k ≤ denominatorJump D left right) : (leftJump left right k).den ≤ D := by
  have hb := (denominatorJump_bounds D left right hD).1
  have he := Nat.mul_le_mul_right right.den hk
  change left.den + k * right.den ≤ D
  change left.den + denominatorJump D left right * right.den ≤ D at hb
  omega

theorem rightJump_den_bound (D : ℕ) (left right : Fraction) (hD : right.den ≤ D) (k : ℕ)
    (hk : k ≤ denominatorJump D right left) : (rightJump left right k).den ≤ D :=
  leftJump_den_bound D right left hD k hk

theorem terminalPredecessor_contract (D : ℕ) (left right : Fraction) (h : Adjacent left right)
    (hl : left.den ≤ D) :
    (terminalPredecessor D left right).den ≤ D ∧
      (terminalPredecessor D left right).value < right.value ∧
        ∀ middle : Fraction, middle.den ≤ D → middle.value < right.value →
          middle.value ≤ (terminalPredecessor D left right).value := by
  have hb := denominatorJump_bounds D left right hl
  have ha := leftJump_adjacent h (denominatorJump D left right)
  exact ⟨hb.1, adjacent_lt ha, fun middle hm hv => left_greatest_below D ha hb.2 _ le_rfl middle hm hv⟩

theorem left_gap_positive (left : Fraction) (cutoff : ℚ) (h : left.value < cutoff) :
    0 < cutoff * left.den - left.num := by
  have hd : (0 : ℚ) < left.den := by exact_mod_cast left.den_pos
  have hc := (div_lt_iff₀ hd).mp h
  linarith

theorem right_gap_positive (right : Fraction) (cutoff : ℚ) (h : cutoff < right.value) :
    0 < right.num - cutoff * right.den := by
  have hd : (0 : ℚ) < right.den := by exact_mod_cast right.den_pos
  have hc := (lt_div_iff₀ hd).mp h
  linarith

theorem leftJump_le_iff (left right : Fraction) (cutoff : ℚ) (hRight : cutoff < right.value) (k : ℕ) :
    (leftJump left right k).value ≤ cutoff ↔ (k : ℚ) ≤ leftRatio left right cutoff := by
  have hp := right_gap_positive right cutoff hRight
  have hd : (0 : ℚ) < (leftJump left right k).den := by exact_mod_cast (leftJump left right k).den_pos
  unfold Fraction.value
  rw [div_le_iff₀ hd]
  unfold leftRatio leftJump
  dsimp
  rw [le_div_iff₀ hp]
  push_cast
  constructor <;> intro hc <;> nlinarith

theorem le_rightJump_iff (left right : Fraction) (cutoff : ℚ) (hLeft : left.value < cutoff) (k : ℕ) :
    cutoff ≤ (rightJump left right k).value ↔ (k : ℚ) ≤ rightRatio left right cutoff := by
  have hp := left_gap_positive left cutoff hLeft
  have hd : (0 : ℚ) < (rightJump left right k).den := by exact_mod_cast (rightJump left right k).den_pos
  unfold Fraction.value
  rw [le_div_iff₀ hd]
  unfold rightRatio rightJump
  dsimp
  rw [le_div_iff₀ hp]
  push_cast
  constructor <;> intro hc <;> nlinarith

theorem quotient_positive (D : ℕ) (first second : Fraction) (hD : first.den + second.den ≤ D) :
    1 ≤ denominatorJump D first second := by
  unfold denominatorJump
  apply (Nat.le_div_iff_mul_le second.den_pos).mpr
  omega

theorem leftQuotient_contract (D : ℕ) (left right : Fraction) (cutoff : ℚ)
    (hDen : left.den + right.den ≤ D) (hLeft : (mediant left right).value < cutoff)
    (hRight : cutoff < right.value) :
    1 ≤ leftQuotient D left right cutoff ∧
      (leftJump left right (leftQuotient D left right cutoff)).den ≤ D ∧
        (leftJump left right (leftQuotient D left right cutoff)).value ≤ cutoff := by
  have hOne : (1 : ℚ) ≤ leftRatio left right cutoff := by
    have he := (leftJump_le_iff left right cutoff hRight 1).mp (by simpa [leftJump, mediant] using hLeft.le)
    simpa using he
  have hFloor : 1 ≤ Nat.floor (leftRatio left right cutoff) := (Nat.one_le_floor_iff _).mpr hOne
  have hBudget := quotient_positive D left right hDen
  have hk : 1 ≤ leftQuotient D left right cutoff := le_min hFloor hBudget
  have hBound := leftJump_den_bound D left right (by omega) (leftQuotient D left right cutoff)
    (min_le_right (Nat.floor (leftRatio left right cutoff)) (denominatorJump D left right))
  have hCast : (leftQuotient D left right cutoff : ℚ) ≤ Nat.floor (leftRatio left right cutoff) := by
    exact_mod_cast min_le_left (Nat.floor (leftRatio left right cutoff)) (denominatorJump D left right)
  have hVal := (leftJump_le_iff left right cutoff hRight (leftQuotient D left right cutoff)).mpr
    (hCast.trans
      (Nat.floor_le (by linarith : (0 : ℚ) ≤ leftRatio left right cutoff)))
  exact ⟨hk, hBound, hVal⟩

theorem rightQuotient_contract (D : ℕ) (left right : Fraction) (cutoff : ℚ)
    (hDen : left.den + right.den ≤ D) (hLeft : left.value < cutoff)
    (hRight : cutoff < (mediant left right).value) :
    1 ≤ rightQuotient D left right cutoff ∧
      (rightJump left right (rightQuotient D left right cutoff)).den ≤ D ∧
        cutoff ≤ (rightJump left right (rightQuotient D left right cutoff)).value := by
  have hOne : (1 : ℚ) ≤ rightRatio left right cutoff := by
    have he := (le_rightJump_iff left right cutoff hLeft 1).mp (by simpa [rightJump, mediant, add_comm] using hRight.le)
    simpa using he
  have hFloor : 1 ≤ Nat.floor (rightRatio left right cutoff) := (Nat.one_le_floor_iff _).mpr hOne
  have hBudget := quotient_positive D right left (by omega)
  have hk : 1 ≤ rightQuotient D left right cutoff := le_min hFloor hBudget
  have hBound := rightJump_den_bound D left right (by omega) (rightQuotient D left right cutoff)
    (min_le_right (Nat.floor (rightRatio left right cutoff)) (denominatorJump D right left))
  have hCast : (rightQuotient D left right cutoff : ℚ) ≤ Nat.floor (rightRatio left right cutoff) := by
    exact_mod_cast min_le_left (Nat.floor (rightRatio left right cutoff)) (denominatorJump D right left)
  have hVal := (le_rightJump_iff left right cutoff hLeft (rightQuotient D left right cutoff)).mpr
    (hCast.trans
      (Nat.floor_le (by linarith : (0 : ℚ) ≤ rightRatio left right cutoff)))
  exact ⟨hk, hBound, hVal⟩

end Blotto.Farey
