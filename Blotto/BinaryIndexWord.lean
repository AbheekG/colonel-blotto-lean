import Blotto.FixedBinaryWord
import Blotto.BinaryCoinWordWork

/-! Fixed-width Boolean index primitives realize equality, unsigned strict
comparison and increment. No natural index is assembled or manipulated by
these runtime primitives. Value/overflow and cell-visit bounds are derived;
physical word/address/allocator interpretation remains separate. -/

namespace Blotto.BinaryIndexWord
open BinaryBorrowWord

def incrementBits : List Bool → List Bool × Bool
  | [] => ([],true)
  | false :: rest => (true :: rest,false)
  | true :: rest =>
      let later := incrementBits rest
      (false :: later.1,later.2)

theorem incrementBits_length (bits : List Bool) : (incrementBits bits).1.length = bits.length := by
  induction bits with
  | nil => rfl
  | cons bit rest ih => cases bit <;> simp only [incrementBits,List.length_cons,ih]

theorem incrementBits_balance (bits : List Bool) : BinaryBigEndian.littleValue bits + 1 =
    BinaryBigEndian.littleValue (incrementBits bits).1 + 2 ^ bits.length * digit (incrementBits bits).2 := by
  induction bits with
  | nil => rfl
  | cons bit rest ih =>
      cases bit
      · simp only [incrementBits,BinaryBigEndian.littleValue,digit,Bool.false_eq_true,ite_false,ite_true,List.length_cons,Nat.mul_zero,Nat.add_zero]
      · simp only [incrementBits,BinaryBigEndian.littleValue,Bool.false_eq_true,ite_false,ite_true,List.length_cons,pow_succ,Nat.add_zero]
        nlinarith

def increment {w : ℕ} (word : FixedBinaryWord w) : FixedBinaryWord w × Bool :=
  let next := incrementBits word.bits
  (⟨next.1,(incrementBits_length word.bits).trans word.size⟩,next.2)

theorem increment_value {w : ℕ} (word : FixedBinaryWord w) (hRoom : word.value + 1 < 2 ^ w) :
    (increment word).1.value = word.value + 1 ∧ (increment word).2 = false := by
  have hb := incrementBits_balance word.bits
  rw [word.size] at hb
  change word.value + 1 = (increment word).1.value + 2 ^ w * digit (increment word).2 at hb
  cases hc : (increment word).2
  · simp only [hc,digit,Bool.false_eq_true,ite_false,Nat.mul_zero,Nat.add_zero] at hb
    exact ⟨hb.symm,rfl⟩
  · simp only [hc,digit,ite_true,Nat.mul_one] at hb
    omega

def incrementVisits : List Bool → ℕ
  | [] => 1
  | false :: _ => 1
  | true :: rest => incrementVisits rest + 1

theorem incrementVisits_bound (bits : List Bool) : incrementVisits bits ≤ bits.length + 1 := by
  induction bits with
  | nil => rfl
  | cons bit rest ih => cases bit <;> simp only [incrementVisits,List.length_cons] <;> omega

def incrementWithWork {w : ℕ} (word : FixedBinaryWord w) : (FixedBinaryWord w × Bool) × ℕ :=
  (increment word,4 * incrementVisits word.bits + 2 * word.bits.length + 2)

theorem incrementWithWork_state {w : ℕ} (word : FixedBinaryWord w) : (incrementWithWork word).1 = increment word := rfl

theorem incrementWithWork_bound {w : ℕ} (word : FixedBinaryWord w) : (incrementWithWork word).2 ≤ 6 * (w + 1) := by
  have h := incrementVisits_bound word.bits
  rw [word.size] at h
  unfold incrementWithWork
  rw [word.size]
  omega

def lt {w : ℕ} (first second : FixedBinaryWord w) : Bool :=
  (BinaryBorrowWord.subtract first.bits second.bits false).2

theorem lt_value {w : ℕ} (first second : FixedBinaryWord w) : lt first second = true ↔ first.value < second.value := by
  have hn := BinaryBorrowWord.subtract_noBorrow_iff first.bits second.bits false (first.size.trans second.size.symm)
  change lt first second = false ↔ second.value + digit false ≤ first.value at hn
  change lt first second = false ↔ second.value ≤ first.value at hn
  cases hc : lt first second <;> simp_all

def ltWithWork {w : ℕ} (first second : FixedBinaryWord w) : Bool × ℕ :=
  (lt first second,10 * BinaryBorrowWord.visits first.bits second.bits + 2 * first.bits.length)

theorem ltWithWork_state {w : ℕ} (first second : FixedBinaryWord w) : (ltWithWork first second).1 = lt first second := rfl

theorem ltWithWork_bound {w : ℕ} (first second : FixedBinaryWord w) : (ltWithWork first second).2 ≤ 12 * (w + 1) := by
  have h := BinaryBorrowWord.visits_eq first.bits second.bits (first.size.trans second.size.symm)
  unfold ltWithWork
  rw [h,first.size]
  omega

def sameWithWork {w : ℕ} (first second : FixedBinaryWord w) : Bool × ℕ :=
  (first.same second,4 * FixedBinaryWord.sameVisits first.bits second.bits)

theorem sameWithWork_value {w : ℕ} (first second : FixedBinaryWord w) : (sameWithWork first second).1 = true ↔ first.value = second.value :=
  first.same_value second

theorem sameWithWork_bound {w : ℕ} (first second : FixedBinaryWord w) : (sameWithWork first second).2 ≤ 4 * (w + 1) := by
  have h := FixedBinaryWord.sameVisits_bound first.bits second.bits
  rw [first.size] at h
  exact Nat.mul_le_mul_left 4 h

end Blotto.BinaryIndexWord
