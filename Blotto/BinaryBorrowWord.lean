import Blotto.BinaryBigEndianCoreValue

/-! Fixed-width little-endian Boolean subtraction. Borrow is propagated with
Boolean operations alone. The recursive expression is a proof specification;
the primary implementation carries a reversed accumulator in tail position. -/

namespace Blotto.BinaryBorrowWord

def digit (b : Bool) : ℕ := if b then 1 else 0

def difference (a b borrow : Bool) : Bool := Bool.xor (Bool.xor a b) borrow

def nextBorrow (a b borrow : Bool) : Bool := (!a && b) || ((!a || b) && borrow)

theorem bit_balance (a b borrow : Bool) :
    digit a + 2 * digit (nextBorrow a b borrow) = digit b + digit borrow + digit (difference a b borrow) := by
  cases a <;> cases b <;> cases borrow <;> rfl

-- Both lists must have the same width. Unmatched suffixes are outside this API.
def reference : List Bool → List Bool → Bool → List Bool × Bool
  | [], [], borrow => ([], borrow)
  | a :: as, b :: bs, borrow =>
    let rest := reference as bs (nextBorrow a b borrow)
    (difference a b borrow :: rest.1, rest.2)
  | _, _, borrow => ([], borrow)

def loop : List Bool → List Bool → Bool → List Bool → List Bool × Bool
  | [], [], borrow, acc => (acc.reverse, borrow)
  | a :: as, b :: bs, borrow, acc =>
    loop as bs (nextBorrow a b borrow) (difference a b borrow :: acc)
  | _, _, borrow, acc => (acc.reverse, borrow)

def subtract (a b : List Bool) (borrow : Bool := false) : List Bool × Bool := loop a b borrow []

theorem loop_refines (a b : List Bool) (borrow : Bool) (acc : List Bool) :
    loop a b borrow acc = (acc.reverse ++ (reference a b borrow).1, (reference a b borrow).2) := by
  induction a generalizing b borrow acc with
  | nil => cases b <;> simp [loop, reference]
  | cons bit rest ih =>
    cases b with
    | nil => simp [loop, reference]
    | cons other tail =>
      rw [loop, ih]
      simp only [reference, List.reverse_cons, List.append_assoc, List.singleton_append]

theorem subtract_refines (a b : List Bool) (borrow : Bool) : subtract a b borrow = reference a b borrow := by
  rw [subtract, loop_refines]
  simp

theorem reference_length (a b : List Bool) (borrow : Bool) (h : a.length = b.length) :
    (reference a b borrow).1.length = a.length := by
  induction a generalizing b borrow with
  | nil => have hb : b = [] := List.eq_nil_of_length_eq_zero (by simpa using h.symm)
           subst b; rfl
  | cons bit rest ih =>
    cases b with
    | nil => simp at h
    | cons other tail =>
      have ht : rest.length = tail.length := by simpa using h
      simpa only [reference, List.length_cons] using congrArg Nat.succ (ih tail (nextBorrow bit other borrow) ht)

theorem reference_balance (a b : List Bool) (borrow : Bool) (h : a.length = b.length) :
    BinaryBigEndian.littleValue a + 2 ^ a.length * digit (reference a b borrow).2 =
      BinaryBigEndian.littleValue b + digit borrow + BinaryBigEndian.littleValue (reference a b borrow).1 := by
  induction a generalizing b borrow with
  | nil =>
    have hb : b = [] := List.eq_nil_of_length_eq_zero (by simpa using h.symm)
    subst b
    simp [reference, BinaryBigEndian.littleValue]
  | cons bit rest ih =>
    cases b with
    | nil => simp at h
    | cons other tail =>
      have ht : rest.length = tail.length := by simpa using h
      have hb := bit_balance bit other borrow
      have hr := ih tail (nextBorrow bit other borrow) ht
      simp only [reference, BinaryBigEndian.littleValue, List.length_cons, pow_succ]
      change (2 * BinaryBigEndian.littleValue rest + digit bit) +
        (2 ^ rest.length * 2) * digit (reference rest tail (nextBorrow bit other borrow)).2 =
        (2 * BinaryBigEndian.littleValue tail + digit other) + digit borrow +
          (2 * BinaryBigEndian.littleValue (reference rest tail (nextBorrow bit other borrow)).1 + digit (difference bit other borrow))
      nlinarith

theorem subtract_length (a b : List Bool) (borrow : Bool) (h : a.length = b.length) :
    (subtract a b borrow).1.length = a.length := by rw [subtract_refines]; exact reference_length a b borrow h

theorem subtract_balance (a b : List Bool) (borrow : Bool) (h : a.length = b.length) :
    BinaryBigEndian.littleValue a + 2 ^ a.length * digit (subtract a b borrow).2 =
      BinaryBigEndian.littleValue b + digit borrow + BinaryBigEndian.littleValue (subtract a b borrow).1 := by
  rw [subtract_refines]
  exact reference_balance a b borrow h

def visits : List Bool → List Bool → ℕ
  | _a :: as, _b :: bs => 1 + visits as bs
  | _, _ => 1

theorem visits_eq (a b : List Bool) (h : a.length = b.length) : visits a b = a.length + 1 := by
  induction a generalizing b with
  | nil => cases b <;> rfl
  | cons bit rest ih =>
    cases b with
    | nil => simp at h
    | cons other tail =>
      have ht : rest.length = tail.length := by simpa using h
      rw [visits, ih tail ht]
      simp [List.length_cons, Nat.add_comm]

end Blotto.BinaryBorrowWord
