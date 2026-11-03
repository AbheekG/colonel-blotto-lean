import Blotto.BinaryWordHighBit
import Blotto.BinaryBorrowWord

/-! Little-endian Boolean full addition, including unequal input widths and
the final carry. Runtime carries a reversed accumulator; numerical values are
proof specifications. Bit-cell operation/copy counts are explicit. -/

namespace Blotto.BinaryAddition

def sumBit (a b carry : Bool) : Bool := Bool.xor (Bool.xor a b) carry
def nextCarry (a b carry : Bool) : Bool := (a && b) || (a && carry) || (b && carry)

theorem bit_balance (a b carry : Bool) :
    BinaryBorrowWord.digit a + BinaryBorrowWord.digit b + BinaryBorrowWord.digit carry =
      BinaryBorrowWord.digit (sumBit a b carry) + 2 * BinaryBorrowWord.digit (nextCarry a b carry) := by
  cases a <;> cases b <;> cases carry <;> rfl

def reference : List Bool → List Bool → Bool → List Bool
  | [], [], carry => if carry then [true] else []
  | a :: rest, [], carry => sumBit a false carry :: reference rest [] (nextCarry a false carry)
  | [], b :: rest, carry => sumBit false b carry :: reference [] rest (nextCarry false b carry)
  | a :: as, b :: bs, carry => sumBit a b carry :: reference as bs (nextCarry a b carry)

def loop : List Bool → List Bool → Bool → List Bool → List Bool
  | [], [], carry, acc => if carry then (true :: acc).reverse else acc.reverse
  | a :: rest, [], carry, acc => loop rest [] (nextCarry a false carry) (sumBit a false carry :: acc)
  | [], b :: rest, carry, acc => loop [] rest (nextCarry false b carry) (sumBit false b carry :: acc)
  | a :: as, b :: bs, carry, acc => loop as bs (nextCarry a b carry) (sumBit a b carry :: acc)

def add (a b : List Bool) : List Bool := loop a b false []

theorem loop_refines (a b : List Bool) (carry : Bool) (acc : List Bool) :
    loop a b carry acc = acc.reverse ++ reference a b carry := by
  induction a generalizing b carry acc with
  | nil =>
    induction b generalizing carry acc with
    | nil => cases carry <;> simp [loop, reference]
    | cons bit rest ih =>
      rw [loop, ih]
      simp only [reference, List.reverse_cons, List.append_assoc, List.singleton_append]
  | cons bit rest ih =>
    cases b with
    | nil => rw [loop, ih]; simp only [reference, List.reverse_cons, List.append_assoc, List.singleton_append]
    | cons other tail => rw [loop, ih]; simp only [reference, List.reverse_cons, List.append_assoc, List.singleton_append]

theorem add_refines (a b : List Bool) : add a b = reference a b false := by rw [add, loop_refines]; rfl

theorem reference_value (a b : List Bool) (carry : Bool) :
    BinaryBigEndian.littleValue (reference a b carry) =
      BinaryBigEndian.littleValue a + BinaryBigEndian.littleValue b + BinaryBorrowWord.digit carry := by
  induction a generalizing b carry with
  | nil =>
    induction b generalizing carry with
    | nil => cases carry <;> simp [reference, BinaryBigEndian.littleValue, BinaryBorrowWord.digit]
    | cons bit rest ih =>
      have hc := bit_balance false bit carry
      rw [reference]
      change 2 * BinaryBigEndian.littleValue (reference [] rest (nextCarry false bit carry)) +
        BinaryBorrowWord.digit (sumBit false bit carry) = _
      rw [ih]
      simp only [BinaryBigEndian.littleValue]
      change _ = 0 + (2 * BinaryBigEndian.littleValue rest + BinaryBorrowWord.digit bit) + BinaryBorrowWord.digit carry
      change 0 + BinaryBorrowWord.digit bit + BinaryBorrowWord.digit carry = _ at hc
      omega
  | cons bit rest ih =>
    cases b with
    | nil =>
      have hc := bit_balance bit false carry
      rw [reference]
      change 2 * BinaryBigEndian.littleValue (reference rest [] (nextCarry bit false carry)) +
        BinaryBorrowWord.digit (sumBit bit false carry) = _
      rw [ih]
      simp only [BinaryBigEndian.littleValue] at *
      change _ = (2 * BinaryBigEndian.littleValue rest + BinaryBorrowWord.digit bit) + 0 + BinaryBorrowWord.digit carry
      change BinaryBorrowWord.digit bit + 0 + BinaryBorrowWord.digit carry = _ at hc
      omega
    | cons other tail =>
      have hc := bit_balance bit other carry
      rw [reference]
      change 2 * BinaryBigEndian.littleValue (reference rest tail (nextCarry bit other carry)) +
        BinaryBorrowWord.digit (sumBit bit other carry) = _
      rw [ih]
      change _ = (2 * BinaryBigEndian.littleValue rest + BinaryBorrowWord.digit bit) +
        (2 * BinaryBigEndian.littleValue tail + BinaryBorrowWord.digit other) + BinaryBorrowWord.digit carry
      omega

theorem add_value (a b : List Bool) : BinaryBigEndian.littleValue (add a b) =
    BinaryBigEndian.littleValue a + BinaryBigEndian.littleValue b := by
  rw [add_refines, reference_value]
  rfl

theorem reference_length (a b : List Bool) (carry : Bool) : (reference a b carry).length ≤ max a.length b.length + 1 := by
  induction a generalizing b carry with
  | nil =>
    induction b generalizing carry with
    | nil => cases carry <;> simp [reference]
    | cons bit rest ih => have h := ih (nextCarry false bit carry); simp only [reference, List.length_cons, List.length_nil] at h ⊢; omega
  | cons bit rest ih =>
    cases b with
    | nil => have h := ih [] (nextCarry bit false carry); simp only [reference, List.length_cons, List.length_nil] at h ⊢; omega
    | cons other tail => have h := ih tail (nextCarry bit other carry); simp only [reference, List.length_cons] at h ⊢; omega

theorem add_length (a b : List Bool) : (add a b).length ≤ max a.length b.length + 1 := by rw [add_refines]; exact reference_length a b false

def visits : List Bool → List Bool → ℕ
  | [], [] => 1
  | _ :: rest, [] => 1 + visits rest []
  | [], _ :: rest => 1 + visits [] rest
  | _ :: as, _ :: bs => 1 + visits as bs

theorem visits_eq (a b : List Bool) : visits a b = max a.length b.length + 1 := by
  induction a generalizing b with
  | nil => induction b with
    | nil => simp [visits]
    | cons bit rest ih => simp only [visits, List.length_cons, List.length_nil, ih]; omega
  | cons bit rest ih => cases b with
    | nil => simp only [visits, List.length_cons, List.length_nil, ih]; omega
    | cons other tail => simp only [visits, List.length_cons, ih]; omega

def bitWork (a b : List Bool) : ℕ := 20 * visits a b + 2 * (max a.length b.length + 1)

theorem bitWork_bound (a b : List Bool) : bitWork a b ≤ 22 * (max a.length b.length + 1) := by rw [bitWork, visits_eq]; omega

end Blotto.BinaryAddition
