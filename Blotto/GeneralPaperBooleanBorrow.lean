import Blotto.GeneralPaperEqualRealSamplingContract
import Blotto.FixedBinaryWord
import Blotto.BinaryCompareBitsMeasured

/-! Fixed-width subtraction and comparison by Boolean operations. The
returned cost observes reached digit/borrow/copy/control actions. No native
integer decoder or arithmetic is used to decide or form the difference. -/
namespace Blotto.GeneralPaperBooleanBorrow
open BinaryBorrowWord
set_option autoImplicit false
set_option maxHeartbeats 700000

structure Result where
  bits : List Bool
  borrow : Bool
  work : ℕ

def loop : List Bool → List Bool → Bool → List Bool → Result
  | a :: as, b :: bs, borrow, acc =>
    let later := loop as bs (nextBorrow a b borrow) (difference a b borrow :: acc)
    ⟨later.bits, later.borrow, later.work + 18⟩
  | _, _, borrow, acc =>
    let returned := BinaryCompareBitsMeasured.reverse acc []
    ⟨returned.1, borrow, returned.2 + 6⟩

theorem loop_data (a b : List Bool) (borrow : Bool) (acc : List Bool) :
    ((loop a b borrow acc).bits, (loop a b borrow acc).borrow) = BinaryBorrowWord.loop a b borrow acc := by
  induction a generalizing b borrow acc with
  | nil => cases b <;> simp [loop, BinaryBorrowWord.loop, BinaryCompareBitsMeasured.reverse_data]
  | cons bit rest ih => cases b with
    | nil => simp [loop, BinaryBorrowWord.loop, BinaryCompareBitsMeasured.reverse_data]
    | cons other tail => exact ih tail (nextBorrow bit other borrow) (difference bit other borrow :: acc)

theorem loop_work (a b : List Bool) (borrow : Bool) (acc : List Bool) (h : a.length = b.length) :
    (loop a b borrow acc).work = 22 * a.length + 4 * acc.length + 8 := by
  induction a generalizing b borrow acc with
  | nil =>
    have hb : b = [] := List.eq_nil_of_length_eq_zero (by simpa using h.symm)
    subst b
    simp only [loop, BinaryCompareBitsMeasured.reverse_work, List.length_nil]
    omega
  | cons bit rest ih => cases b with
    | nil => simp at h
    | cons other tail =>
      have hh := ih tail (nextBorrow bit other borrow) (difference bit other borrow :: acc) (by simpa using h)
      simp only [loop, List.length_cons] at hh ⊢
      omega

def subtract {W : ℕ} (a b : FixedBinaryWord W) : FixedBinaryWord W × Bool × ℕ :=
  let result := loop a.bits b.bits false []
  have hData : result.bits = (BinaryBorrowWord.subtract a.bits b.bits false).1 :=
    congrArg Prod.fst (loop_data a.bits b.bits false [])
  have hLength : result.bits.length = W := by
    rw [hData]
    exact (BinaryBorrowWord.subtract_length a.bits b.bits false (a.size.trans b.size.symm)).trans a.size
  (⟨result.bits, hLength⟩, result.borrow, result.work)

theorem subtract_data {W : ℕ} (a b : FixedBinaryWord W) :
    ((subtract a b).1.bits, (subtract a b).2.1) = BinaryBorrowWord.subtract a.bits b.bits false :=
  loop_data a.bits b.bits false []

theorem subtract_work {W : ℕ} (a b : FixedBinaryWord W) : (subtract a b).2.2 = 22 * W + 8 := by
  have h := loop_work a.bits b.bits false [] (a.size.trans b.size.symm)
  simpa only [subtract, a.size, List.length_nil, Nat.mul_zero, Nat.add_zero] using h

theorem borrow_iff {W : ℕ} (a b : FixedBinaryWord W) : (subtract a b).2.1 = true ↔ a.value < b.value := by
  have h := BinaryBorrowWord.subtract_noBorrow_iff a.bits b.bits false (a.size.trans b.size.symm)
  have hb := congrArg Prod.snd (subtract_data a b)
  rw [← hb] at h
  simp only [digit, Bool.false_eq_true, ite_false, Nat.add_zero] at h
  cases he : (subtract a b).2.1 <;> simp only [he, Bool.false_eq_true, Bool.true_eq_false, true_iff, false_iff] at h ⊢
  · exact not_lt_of_ge h
  · exact Nat.lt_of_not_ge h

theorem difference_value {W : ℕ} (a b : FixedBinaryWord W) (h : b.value ≤ a.value) :
    (subtract a b).1.value = a.value - b.value := by
  have hn : (subtract a b).2.1 = false := Bool.eq_false_of_not_eq_true (fun hh => not_lt_of_ge h ((borrow_iff a b).mp hh))
  have hb := congrArg Prod.snd (subtract_data a b)
  have hd := congrArg Prod.fst (subtract_data a b)
  change (subtract a b).1.bits = (BinaryBorrowWord.subtract a.bits b.bits false).1 at hd
  change BinaryBigEndian.littleValue (subtract a b).1.bits = _
  rw [hd]
  exact BinaryBorrowWord.subtract_value a.bits b.bits false (a.size.trans b.size.symm) (hb.symm.trans hn)

end Blotto.GeneralPaperBooleanBorrow
