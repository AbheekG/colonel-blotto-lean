import Blotto.FareyPredecessor

/-! Exact quotient jumps alternate sides unless the denominator budget has
already been exhausted. The side being updated is therefore the smaller
denominator, and its binary word width increases at every continuing step.
These are algorithm facts, not caller-supplied work certificates. -/

namespace Blotto.Farey

def StepOrdered (D : ℕ) (cutoff : ℚ) (left right : Fraction) : Prop :=
  left.den + right.den ≤ D →
    ((mediant left right).value < cutoff → left.den ≤ right.den) ∧
      (cutoff < (mediant left right).value → right.den ≤ left.den)

theorem left_successor_value (left right : Fraction) (k : ℕ) :
    (leftJump left right (k + 1)).value = (mediant (leftJump left right k) right).value := by
  unfold Fraction.value leftJump mediant
  dsimp
  congr 1 <;> push_cast <;> ring

theorem right_successor_value (left right : Fraction) (k : ℕ) :
    (rightJump left right (k + 1)).value = (mediant left (rightJump left right k)).value := by
  unfold Fraction.value rightJump mediant
  dsimp
  congr 1 <;> push_cast <;> ring

theorem leftQuotient_full_floor (D : ℕ) (left right : Fraction) (cutoff : ℚ)
    (hDen : left.den ≤ D)
    (hNext : (leftJump left right (leftQuotient D left right cutoff)).den + right.den ≤ D) :
    leftQuotient D left right cutoff = Nat.floor (leftRatio left right cutoff) := by
  have hb := (denominatorJump_bounds D left right hDen).2
  by_contra hf
  have he : leftQuotient D left right cutoff = denominatorJump D left right := by
    unfold leftQuotient at *
    omega
  rw [he] at hNext
  omega

theorem rightQuotient_full_floor (D : ℕ) (left right : Fraction) (cutoff : ℚ)
    (hDen : right.den ≤ D)
    (hNext : left.den + (rightJump left right (rightQuotient D left right cutoff)).den ≤ D) :
    rightQuotient D left right cutoff = Nat.floor (rightRatio left right cutoff) := by
  have hb := (denominatorJump_bounds D right left hDen).2
  by_contra hf
  have he : rightQuotient D left right cutoff = denominatorJump D right left := by
    unfold rightQuotient at *
    omega
  change left.den + (leftJump right left (rightQuotient D left right cutoff)).den ≤ D at hNext
  rw [he] at hNext
  omega

theorem leftQuotient_opposite (D : ℕ) (left right : Fraction) (cutoff : ℚ)
    (hDen : left.den ≤ D) (hRight : cutoff < right.value)
    (hNext : (leftJump left right (leftQuotient D left right cutoff)).den + right.den ≤ D) :
    cutoff < (mediant (leftJump left right (leftQuotient D left right cutoff)) right).value := by
  have he := leftQuotient_full_floor D left right cutoff hDen hNext
  have hf := Nat.lt_floor_add_one (leftRatio left right cutoff)
  have hn : ¬ ((leftQuotient D left right cutoff + 1 : ℕ) : ℚ) ≤ leftRatio left right cutoff := by
    rw [he]
    push_cast
    exact not_le_of_gt hf
  have hx : cutoff < (leftJump left right (leftQuotient D left right cutoff + 1)).value := by
    apply lt_of_not_ge
    intro h
    exact hn ((leftJump_le_iff left right cutoff hRight _).mp h)
  rwa [left_successor_value] at hx

theorem rightQuotient_opposite (D : ℕ) (left right : Fraction) (cutoff : ℚ)
    (hDen : right.den ≤ D) (hLeft : left.value < cutoff)
    (hNext : left.den + (rightJump left right (rightQuotient D left right cutoff)).den ≤ D) :
    (mediant left (rightJump left right (rightQuotient D left right cutoff))).value < cutoff := by
  have he := rightQuotient_full_floor D left right cutoff hDen hNext
  have hf := Nat.lt_floor_add_one (rightRatio left right cutoff)
  have hn : ¬ ((rightQuotient D left right cutoff + 1 : ℕ) : ℚ) ≤ rightRatio left right cutoff := by
    rw [he]
    push_cast
    exact not_le_of_gt hf
  have hx : (rightJump left right (rightQuotient D left right cutoff + 1)).value < cutoff := by
    apply lt_of_not_ge
    intro h
    exact hn ((le_rightJump_iff left right cutoff hLeft _).mp h)
  rwa [right_successor_value] at hx

theorem leftQuotient_next_ordered (D : ℕ) (left right : Fraction) (cutoff : ℚ)
    (hDen : left.den + right.den ≤ D) (hBelow : (mediant left right).value < cutoff)
    (hRight : cutoff < right.value) :
    StepOrdered D cutoff (leftJump left right (leftQuotient D left right cutoff)) right := by
  intro hNext
  have hOpp := leftQuotient_opposite D left right cutoff (by omega) hRight hNext
  have hk := (leftQuotient_contract D left right cutoff hDen hBelow hRight).1
  constructor
  · intro h
    linarith
  · intro _
    change right.den ≤ left.den + leftQuotient D left right cutoff * right.den
    nlinarith

theorem rightQuotient_next_ordered (D : ℕ) (left right : Fraction) (cutoff : ℚ)
    (hDen : left.den + right.den ≤ D) (hLeft : left.value < cutoff)
    (hAbove : cutoff < (mediant left right).value) :
    StepOrdered D cutoff left (rightJump left right (rightQuotient D left right cutoff)) := by
  intro hNext
  have hOpp := rightQuotient_opposite D left right cutoff (by omega) hLeft hNext
  have hk := (rightQuotient_contract D left right cutoff hDen hLeft hAbove).1
  constructor
  · intro _
    change left.den ≤ right.den + rightQuotient D left right cutoff * left.den
    nlinarith
  · intro h
    linarith

theorem binaryWordWidth_growth (first second : ℕ) (hFirst : 0 < first) (hDouble : 2 * first ≤ second) :
    binaryWordWidth first + 1 ≤ binaryWordWidth second := by
  have hLow : 2 ^ first.log2 ≤ first := (Nat.le_log2 (ne_of_gt hFirst)).mp le_rfl
  have hPower : 2 ^ (first.log2 + 1) ≤ second := by
    rw [pow_succ]
    omega
  have hSecond : 0 < second := by omega
  have hLog := (Nat.le_log2 (ne_of_gt hSecond)).mpr hPower
  unfold binaryWordWidth
  omega

theorem leftJump_width_growth (left right : Fraction) (k : ℕ) (hk : 1 ≤ k) (hSmall : left.den ≤ right.den) :
    binaryWordWidth left.den + 1 ≤ binaryWordWidth (leftJump left right k).den := by
  apply binaryWordWidth_growth _ _ left.den_pos
  change 2 * left.den ≤ left.den + k * right.den
  nlinarith

theorem rightJump_width_growth (left right : Fraction) (k : ℕ) (hk : 1 ≤ k) (hSmall : right.den ≤ left.den) :
    binaryWordWidth right.den + 1 ≤ binaryWordWidth (rightJump left right k).den := by
  apply binaryWordWidth_growth _ _ right.den_pos
  change 2 * right.den ≤ right.den + k * left.den
  nlinarith

theorem initial_step_ordered (D : ℕ) (cutoff : ℚ) : StepOrdered D cutoff zeroFraction oneFraction := by
  intro _
  exact ⟨fun _ => le_rfl, fun _ => le_rfl⟩

end Blotto.Farey
