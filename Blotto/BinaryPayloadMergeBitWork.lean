import Blotto.BinaryPayloadCounts
import Blotto.RationalExpressionWordWidth

/-! Operand/result-copy and shift/add prices follow the balanced decoder's
actual merge values. A supplied linear primitive envelope is explicit. This
does not certify a library backend, counters, addressing or allocation. -/

namespace Blotto.BinaryPayload

def mergeBitPrice (primitive : ℕ → ℕ) (buffer : Array Bool) (pos length : ℕ) : ℕ :=
  let low := length / 2
  let x := balancedValue buffer pos low
  let y := balancedValue buffer (pos + low) (length - low)
  let z := y <<< low
  binaryWordWidth x + binaryWordWidth y + binaryWordWidth z + binaryWordWidth (x + z) +
    primitive (binaryWordWidth y + low) + primitive (max (binaryWordWidth x) (binaryWordWidth z))

theorem merge_value (buffer : Array Bool) (pos length : ℕ) (hLength : 1 < length) :
    balancedValue buffer pos length = balancedValue buffer pos (length / 2) +
      (balancedValue buffer (pos + length / 2) (length - length / 2) <<< (length / 2)) := by
  conv_lhs => unfold balancedValue
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]

theorem mergeBitPrice_bound (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w)
    (buffer : Array Bool) (pos length : ℕ) (hLength : 1 < length) :
    mergeBitPrice primitive buffer pos length ≤ (4 + 2 * c) * length := by
  let low := length / 2
  let high := length - low
  let x := balancedValue buffer pos low
  let y := balancedValue buffer (pos + low) high
  let z := y <<< low
  have hLow : 0 < low := by dsimp [low]; omega
  have hHigh : 0 < high := by dsimp [high, low]; omega
  have hSum : high + low = length := by dsimp [high, low]; omega
  have hx := binaryWordWidth_le_of_lt_pow hLow (balancedValue_bounds buffer pos low)
  have hy := binaryWordWidth_le_of_lt_pow hHigh (balancedValue_bounds buffer (pos + low) high)
  change binaryWordWidth x ≤ low at hx
  change binaryWordWidth y ≤ high at hy
  have hzVal : z < 2 ^ length := by
    dsimp only [z]
    rw [Nat.shiftLeft_eq]
    calc
      y * 2 ^ low < 2 ^ high * 2 ^ low := Nat.mul_lt_mul_of_pos_right (balancedValue_bounds _ _ _) (Nat.two_pow_pos low)
      _ = 2 ^ length := by rw [← pow_add, hSum]
  have hz := binaryWordWidth_le_of_lt_pow (by omega : 0 < length) hzVal
  have hOutVal : x + z < 2 ^ length := by
    have h := balancedValue_bounds buffer pos length
    rw [merge_value buffer pos length hLength] at h
    exact h
  have hOut := binaryWordWidth_le_of_lt_pow (by omega : 0 < length) hOutVal
  have hShift := (hPrimitive (binaryWordWidth y + low)).trans
    (Nat.mul_le_mul_left c (show binaryWordWidth y + low ≤ length by omega))
  have hAdd := (hPrimitive (max (binaryWordWidth x) (binaryWordWidth z))).trans
    (Nat.mul_le_mul_left c (show max (binaryWordWidth x) (binaryWordWidth z) ≤ length by omega))
  change binaryWordWidth x + binaryWordWidth y + binaryWordWidth z + binaryWordWidth (x + z) +
    primitive (binaryWordWidth y + low) + primitive (max (binaryWordWidth x) (binaryWordWidth z)) ≤ (4 + 2 * c) * length
  nlinarith [show low ≤ length by dsimp [low]; omega, show high ≤ length by dsimp [high]; omega]

def balancedBitWork (primitive : ℕ → ℕ) (buffer : Array Bool) (pos length : ℕ) : ℕ :=
  if length = 0 then 0 else if length = 1 then 1 else
    balancedBitWork primitive buffer pos (length / 2) +
      balancedBitWork primitive buffer (pos + length / 2) (length - length / 2) +
        mergeBitPrice primitive buffer pos length
termination_by length
decreasing_by all_goals omega

theorem balancedBitWork_bound (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w)
    (buffer : Array Bool) (pos length : ℕ) :
    balancedBitWork primitive buffer pos length ≤ length + (4 + 2 * c) * mergeSize length := by
  unfold balancedBitWork
  split
  · rename_i hz
    subst length
    simp [mergeSize]
  · split
    · rename_i hOne
      subst length
      simp [mergeSize]
    · rename_i hZero hOne
      have hLength : 1 < length := by omega
      have hl := balancedBitWork_bound primitive c hPrimitive buffer pos (length / 2)
      have hh := balancedBitWork_bound primitive c hPrimitive buffer (pos + length / 2) (length - length / 2)
      have hp := mergeBitPrice_bound primitive c hPrimitive buffer pos length hLength
      rw [mergeSize, ite_eq_right (by omega : ¬length ≤ 1)]
      nlinarith [show length / 2 + (length - length / 2) = length by omega]
termination_by length
decreasing_by all_goals omega

theorem balancedBitWork_word_bound (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w)
    (buffer : Array Bool) (pos length : ℕ) :
    balancedBitWork primitive buffer pos length ≤ length + (4 + 2 * c) * length * binaryWordWidth length := by
  have hb := balancedBitWork_bound primitive c hPrimitive buffer pos length
  have hm := Nat.mul_le_mul_left (4 + 2 * c) (mergeSize_word_bound length)
  nlinarith

end Blotto.BinaryPayload
