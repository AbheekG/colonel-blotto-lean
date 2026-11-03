import Blotto.BinaryRationalNormalization
import Blotto.BinaryMultiplication

/-! Signed integer magnitudes use Boolean add, multiply and equal-width borrow
subtraction. Padding depends only on list lengths; represented numeric values
occur solely in specifications. Leading zeros and signed-zero inputs are valid. -/

namespace Blotto.BinarySignedMagnitude

structure Word where
  negative : Bool
  bits : List Bool

def signedValue (negative : Bool) (magnitude : ℕ) : ℤ := if negative then -(magnitude : ℤ) else (magnitude : ℤ)

def value (word : Word) : ℤ := signedValue word.negative (BinaryBigEndian.littleValue word.bits)

def negate (word : Word) : Word := ⟨!word.negative, word.bits⟩

theorem negate_value (word : Word) : value (negate word) = -value word := by
  cases word with
  | mk negative bits => cases negative <;> simp [value, signedValue, negate]

def pad (width : ℕ) (bits : List Bool) : List Bool := bits ++ List.replicate (width - bits.length) false

theorem pad_length (width : ℕ) (bits : List Bool) (h : bits.length ≤ width) :
    (pad width bits).length = width := by simp only [pad, List.length_append, List.length_replicate]; omega

theorem pad_value (width : ℕ) (bits : List Bool) : BinaryBigEndian.littleValue (pad width bits) = BinaryBigEndian.littleValue bits := by
  have hz : ∀ n, BinaryBigEndian.littleValue (List.replicate n false) = 0 := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => simp [List.replicate_succ, BinaryBigEndian.littleValue, ih]
  rw [pad, BinaryWordHighBit.littleValue_append, hz]
  simp

def difference (first second : List Bool) : Word :=
  let width := max first.length second.length
  let a := pad width first
  let b := pad width second
  let result := BinaryBorrowWord.subtract a b false
  if result.2 then ⟨true, (BinaryBorrowWord.subtract b a false).1⟩ else ⟨false, result.1⟩

theorem difference_value (first second : List Bool) :
    value (difference first second) = (BinaryBigEndian.littleValue first : ℤ) - BinaryBigEndian.littleValue second := by
  let width := max first.length second.length
  let a := pad width first
  let b := pad width second
  have ha : a.length = width := pad_length width first (Nat.le_max_left _ _)
  have hb : b.length = width := pad_length width second (Nat.le_max_right _ _)
  have hlen := ha.trans hb.symm
  have hCmp := BinaryBorrowWord.subtract_noBorrow_iff a b false hlen
  simp only [BinaryBorrowWord.digit, Bool.false_eq_true, ite_false, Nat.add_zero] at hCmp
  unfold difference
  change value (if (BinaryBorrowWord.subtract a b false).2 then _ else _) = _
  cases he : (BinaryBorrowWord.subtract a b false).2
  · simp only [Bool.false_eq_true, ite_false]
    have hSub := BinaryBorrowWord.subtract_value a b false hlen he
    have hOrder := hCmp.mp he
    simp only [BinaryBorrowWord.digit, Bool.false_eq_true, ite_false, Nat.add_zero] at hSub
    change (BinaryBigEndian.littleValue (BinaryBorrowWord.subtract a b false).1 : ℤ) = _
    rw [hSub, Nat.cast_sub hOrder, pad_value, pad_value]
  · simp only [ite_true]
    have hOrder : BinaryBigEndian.littleValue a ≤ BinaryBigEndian.littleValue b := by
      by_contra hn
      have hNo := hCmp.mpr (Nat.le_of_lt (Nat.lt_of_not_ge hn))
      rw [he] at hNo
      cases hNo
    have hBack : (BinaryBorrowWord.subtract b a false).2 = false := by
      apply (BinaryBorrowWord.subtract_noBorrow_iff b a false hlen.symm).mpr
      simpa only [BinaryBorrowWord.digit, Bool.false_eq_true, ite_false, Nat.add_zero] using hOrder
    have hSub := BinaryBorrowWord.subtract_value b a false hlen.symm hBack
    simp only [BinaryBorrowWord.digit, Bool.false_eq_true, ite_false, Nat.add_zero] at hSub
    change -(BinaryBigEndian.littleValue (BinaryBorrowWord.subtract b a false).1 : ℤ) = _
    rw [hSub, Nat.cast_sub hOrder, pad_value, pad_value]
    ring

def add (first second : Word) : Word :=
  if first.negative = second.negative then
    ⟨first.negative, BinaryAddition.add first.bits second.bits⟩
  else if first.negative then difference second.bits first.bits else difference first.bits second.bits

theorem add_value (first second : Word) : value (add first second) = value first + value second := by
  cases first with
  | mk signA bitsA =>
    cases second with
    | mk signB bitsB =>
      cases signA <;> cases signB
      · simp [add, value, signedValue, BinaryAddition.add_value, Nat.cast_add]
      · change value (difference bitsA bitsB) = _
        rw [difference_value]
        simp [value, signedValue]
        ring
      · change value (difference bitsB bitsA) = _
        rw [difference_value]
        simp [value, signedValue]
        ring
      · simp [add, value, signedValue, BinaryAddition.add_value, Nat.cast_add]
        ring

def subtract (first second : Word) : Word := add first (negate second)

theorem subtract_value (first second : Word) : value (subtract first second) = value first - value second := by
  rw [subtract, add_value, negate_value]
  ring

def multiply (first second : Word) : Word :=
  ⟨Bool.xor first.negative second.negative, BinaryMultiplication.multiply first.bits second.bits⟩

theorem multiply_value (first second : Word) : value (multiply first second) = value first * value second := by
  cases first with
  | mk signA bitsA =>
    cases second with
    | mk signB bitsB =>
      cases signA <;> cases signB <;>
        simp [multiply, value, signedValue, BinaryMultiplication.multiply_value, Nat.cast_mul]

theorem difference_length (first second : List Bool) :
    (difference first second).bits.length = max first.length second.length := by
  let width := max first.length second.length
  have ha := pad_length width first (Nat.le_max_left _ _)
  have hb := pad_length width second (Nat.le_max_right _ _)
  have hs := BinaryBorrowWord.subtract_length (pad width first) (pad width second) false (ha.trans hb.symm)
  have ht := BinaryBorrowWord.subtract_length (pad width second) (pad width first) false (hb.trans ha.symm)
  unfold difference
  change (if (BinaryBorrowWord.subtract (pad width first) (pad width second) false).2 then
      (⟨true, (BinaryBorrowWord.subtract (pad width second) (pad width first) false).1⟩ : Word)
    else ⟨false, (BinaryBorrowWord.subtract (pad width first) (pad width second) false).1⟩).bits.length = _
  split <;> dsimp only <;> omega

theorem add_length (first second : Word) : (add first second).bits.length ≤ max first.bits.length second.bits.length + 1 := by
  unfold add
  split
  · exact BinaryAddition.add_length _ _
  · split <;> rw [difference_length] <;> omega

theorem multiply_length (first second : Word) :
    (multiply first second).bits.length ≤ 2 * first.bits.length + second.bits.length :=
  BinaryMultiplication.multiply_length _ _

def differenceWork (first second : List Bool) : ℕ :=
  let width := max first.length second.length
  4 * (width + 1) + 22 * (width + 1) +
    if (BinaryBorrowWord.subtract (pad width first) (pad width second) false).2 then 22 * (width + 1) else 0

theorem differenceWork_bound (first second : List Bool) : differenceWork first second ≤ 48 * (max first.length second.length + 1) := by
  unfold differenceWork
  dsimp only
  split <;> omega

def addWork (first second : Word) : ℕ :=
  3 + if first.negative = second.negative then BinaryAddition.bitWork first.bits second.bits
    else if first.negative then differenceWork second.bits first.bits else differenceWork first.bits second.bits

theorem addWork_bound (first second : Word) : addWork first second ≤ 51 * (max first.bits.length second.bits.length + 1) := by
  have ha := BinaryAddition.bitWork_bound first.bits second.bits
  have hd := differenceWork_bound first.bits second.bits
  have hr := differenceWork_bound second.bits first.bits
  rw [Nat.max_comm second.bits.length first.bits.length] at hr
  unfold addWork
  split
  · omega
  · split <;> omega

def multiplyWork (first second : Word) : ℕ := 1 + BinaryMultiplication.work first.bits second.bits

theorem multiplyWork_bound (first second : Word) (W : ℕ)
    (hA : first.bits.length ≤ W) (hB : second.bits.length ≤ W) :
    multiplyWork first second ≤ 100 * (W + 1) ^ 2 := by
  have h := BinaryMultiplication.work_bound first.bits second.bits
  unfold multiplyWork
  nlinarith

end Blotto.BinarySignedMagnitude
