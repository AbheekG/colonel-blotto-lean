import Blotto.BinaryBorrowWord

/-! Equal-width Boolean words represent all unsigned values, including leading
zeros. Final borrow is exactly underflow, and subtraction without borrow has
its usual natural-number value. Numerical values occur only in proofs. -/

namespace Blotto.BinaryBorrowWord

theorem littleValue_bounds (bits : List Bool) : BinaryBigEndian.littleValue bits < 2 ^ bits.length := by
  have h := BinaryBigEndian.value_bounds bits.reverse
  rw [BinaryBigEndian.value_reverse, List.length_reverse] at h
  exact h

theorem littleValue_injective (a b : List Bool) (hLength : a.length = b.length)
    (hValue : BinaryBigEndian.littleValue a = BinaryBigEndian.littleValue b) : a = b := by
  induction a generalizing b with
  | nil => exact (List.eq_nil_of_length_eq_zero (by simpa using hLength.symm)).symm
  | cons bit rest ih =>
    cases b with
    | nil => simp at hLength
    | cons other tail =>
      have ht : rest.length = tail.length := by simpa using hLength
      cases bit <;> cases other <;> simp only [BinaryBigEndian.littleValue, Bool.false_eq_true, ite_false, ite_true, Nat.add_zero] at hValue
      · have hv : BinaryBigEndian.littleValue rest = BinaryBigEndian.littleValue tail := by omega
        rw [ih tail ht hv]
      · omega
      · omega
      · have hv : BinaryBigEndian.littleValue rest = BinaryBigEndian.littleValue tail := by omega
        rw [ih tail ht hv]

theorem subtract_noBorrow_iff (a b : List Bool) (borrow : Bool) (hLength : a.length = b.length) :
    (subtract a b borrow).2 = false ↔ BinaryBigEndian.littleValue b + digit borrow ≤ BinaryBigEndian.littleValue a := by
  have hBalance := subtract_balance a b borrow hLength
  have hBound := littleValue_bounds (subtract a b borrow).1
  rw [subtract_length a b borrow hLength] at hBound
  cases hOut : (subtract a b borrow).2
  · simp only [hOut, show digit false = 0 from rfl, Nat.mul_zero, Nat.add_zero] at hBalance
    constructor
    · intro _; omega
    · intro _; rfl
  · simp only [hOut, show digit true = 1 from rfl, Nat.mul_one] at hBalance
    constructor
    · intro he; cases he
    · intro he; omega

theorem subtract_value (a b : List Bool) (borrow : Bool) (hLength : a.length = b.length)
    (hNoBorrow : (subtract a b borrow).2 = false) :
    BinaryBigEndian.littleValue (subtract a b borrow).1 =
      BinaryBigEndian.littleValue a - (BinaryBigEndian.littleValue b + digit borrow) := by
  have h := subtract_balance a b borrow hLength
  rw [hNoBorrow] at h
  simp only [show digit false = 0 from rfl, Nat.mul_zero, Nat.add_zero] at h
  omega

end Blotto.BinaryBorrowWord
