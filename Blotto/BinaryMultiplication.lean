import Blotto.BinaryAddition

/-! Schoolbook multiplication evaluates little-endian bits with Boolean
shifts and the verified full adder. No natural multiplication is called by
the runtime. Conservative size/work bounds include leading-zero operands. -/

namespace Blotto.BinaryMultiplication

def multiply : List Bool → List Bool → List Bool
  | [], _ => []
  | bit :: rest, other =>
      let shifted := false :: multiply rest other
      if bit then BinaryAddition.add other shifted else shifted

theorem multiply_value (a b : List Bool) : BinaryBigEndian.littleValue (multiply a b) =
    BinaryBigEndian.littleValue a * BinaryBigEndian.littleValue b := by
  induction a with
  | nil => simp [multiply, BinaryBigEndian.littleValue]
  | cons bit rest ih =>
    cases bit
    · simp only [multiply, Bool.false_eq_true, ite_false, BinaryBigEndian.littleValue, Nat.add_zero, ih]
      ring
    · simp only [multiply, ite_true, BinaryAddition.add_value, BinaryBigEndian.littleValue,
        Bool.false_eq_true, ite_false, Nat.add_zero, ih]
      ring

theorem multiply_length (a b : List Bool) : (multiply a b).length ≤ 2 * a.length + b.length := by
  induction a with
  | nil => simp [multiply]
  | cons bit rest ih =>
    have hAdd := BinaryAddition.add_length b (false :: multiply rest b)
    cases bit <;> simp only [multiply, Bool.false_eq_true, ite_false, ite_true, List.length_cons] at hAdd ⊢ <;> omega

def work : List Bool → List Bool → ℕ
  | [], _ => 1
  | bit :: rest, other =>
      work rest other + 3 + if bit then BinaryAddition.bitWork other (false :: multiply rest other) else 0

theorem work_bound (a b : List Bool) : work a b ≤
    1 + a.length * (22 * (2 * a.length + b.length + 2) + 3) := by
  induction a with
  | nil => simp [work]
  | cons bit rest ih =>
    have hLength := multiply_length rest b
    have hAdd := BinaryAddition.bitWork_bound b (false :: multiply rest b)
    have hMax : max b.length (false :: multiply rest b).length + 1 ≤ 2 * (rest.length + 1) + b.length + 2 := by
      simp only [List.length_cons]
      omega
    have hAddBound := hAdd.trans (Nat.mul_le_mul_left 22 hMax)
    cases bit <;> simp only [work, Bool.false_eq_true, ite_false, ite_true, List.length_cons] <;> nlinarith

end Blotto.BinaryMultiplication
