import Blotto.BinaryBigEndianValue
import Blotto.BinaryWidthPrecision
import Blotto.BinaryCarryCounterSize

/-! A positive word has an implicit leading one and a stored Boolean tail.
Its runtime width, shifts and comparisons need no assembled large integer. -/

namespace Blotto

structure PositiveBinaryWord where
  tail : List Bool

namespace PositiveBinaryWord

def bits (w : PositiveBinaryWord) : List Bool := true :: w.tail
def width (w : PositiveBinaryWord) : ℕ := w.tail.length + 1
def countedWidth (w : PositiveBinaryWord) : ℕ := BinaryCarryCounter.lengthFromOne w.tail

theorem countedWidth_eq (w : PositiveBinaryWord) : w.countedWidth = w.width := BinaryCarryCounter.lengthFromOne_eq w.tail

theorem countedWidth_carry_bound (w : PositiveBinaryWord) :
    BinaryCarryCounter.countCarryCells w.tail [true] ≤ 2 * w.width := by
  have h := BinaryCarryCounter.lengthFromOne_carry_bound w.tail
  unfold width
  omega
def value (w : PositiveBinaryWord) : ℕ := BinaryBigEndian.value w.bits
def shifted (w : PositiveBinaryWord) (k : ℕ) : PositiveBinaryWord := ⟨w.tail ++ List.replicate k false⟩

theorem value_pos (w : PositiveBinaryWord) : 0 < w.value := by
  have hp := Nat.two_pow_pos w.tail.length
  change 0 < 2 ^ w.tail.length + BinaryBigEndian.value w.tail
  omega

theorem width_eq (w : PositiveBinaryWord) : w.width = binaryWordWidth w.value := by
  have hLow : 2 ^ w.tail.length ≤ w.value := by change 2 ^ w.tail.length ≤ 2 ^ w.tail.length + BinaryBigEndian.value w.tail; omega
  have hHigh := BinaryBigEndian.value_bounds w.bits
  have hLe := (Nat.le_log2 (ne_of_gt w.value_pos)).mpr hLow
  have hLt := (Nat.log2_lt (ne_of_gt w.value_pos)).mpr hHigh
  simp only [bits, List.length_cons] at hLt
  unfold width binaryWordWidth
  omega

theorem width_shifted (w : PositiveBinaryWord) (k : ℕ) : (w.shifted k).width = w.width + k := by
  simp [shifted, width]
  omega

theorem false_value (k : ℕ) : BinaryBigEndian.value (List.replicate k false) = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => simpa [List.replicate_succ, BinaryBigEndian.value] using ih

theorem value_shifted (w : PositiveBinaryWord) (k : ℕ) : (w.shifted k).value = w.value <<< k := by
  have hBits : (w.shifted k).bits = w.bits ++ List.replicate k false := rfl
  unfold value
  rw [hBits, BinaryBigEndian.value_append, false_value]
  simp [Nat.shiftLeft_eq]

def leScan : List Bool → List Bool → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => if a = b then leScan as bs else !a

theorem leScan_eq (a b : List Bool) (hLength : a.length = b.length) :
    leScan a b = true ↔ BinaryBigEndian.value a ≤ BinaryBigEndian.value b := by
  induction a generalizing b with
  | nil => have hb : b = [] := List.eq_nil_of_length_eq_zero (by simpa using hLength.symm)
           subst b; simp [leScan, BinaryBigEndian.value]
  | cons bit as ih =>
    cases b with
    | nil => simp at hLength
    | cons other bs =>
      have ht : as.length = bs.length := by simpa using hLength
      have hvA := BinaryBigEndian.value_bounds as
      have hvB := BinaryBigEndian.value_bounds bs
      cases bit <;> cases other
      · simpa [leScan, BinaryBigEndian.value] using ih bs ht
      · simp [leScan, BinaryBigEndian.value]
        rw [ht] at hvA
        omega
      · simp [leScan, BinaryBigEndian.value]
        rw [ht]
        omega
      · simpa [leScan, BinaryBigEndian.value, ht] using ih bs ht

def leNumeric (a b : PositiveBinaryWord) : Bool :=
  if a.width < b.width then true else if b.width < a.width then false else leScan a.bits b.bits

def le (a b : PositiveBinaryWord) : Bool :=
  let aw := a.countedWidth
  let bw := b.countedWidth
  if aw < bw then true else if bw < aw then false else leScan a.bits b.bits

theorem le_refines (a b : PositiveBinaryWord) : a.le b = a.leNumeric b := by
  simp only [le, countedWidth_eq]
  rfl

theorem le_eq (a b : PositiveBinaryWord) : a.le b = true ↔ a.value ≤ b.value := by
  have ha := BinaryBigEndian.value_bounds a.bits
  have hb := BinaryBigEndian.value_bounds b.bits
  have hALow : 2 ^ (a.width - 1) ≤ a.value := by
    change 2 ^ (a.tail.length + 1 - 1) ≤ 2 ^ a.tail.length + BinaryBigEndian.value a.tail
    simp
  have hBLow : 2 ^ (b.width - 1) ≤ b.value := by
    change 2 ^ (b.tail.length + 1 - 1) ≤ 2 ^ b.tail.length + BinaryBigEndian.value b.tail
    simp
  change a.value < 2 ^ a.width at ha
  change b.value < 2 ^ b.width at hb
  rw [le_refines]
  unfold leNumeric
  split
  · rename_i hlt
    have hp := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (show a.width ≤ b.width - 1 by omega)
    simp only [true_iff]
    omega
  · split
    · rename_i hlt
      have hp := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (show b.width ≤ a.width - 1 by omega)
      simp only [Bool.false_eq_true, false_iff]
      omega
    · have he : a.bits.length = b.bits.length := by change a.width = b.width; omega
      exact leScan_eq a.bits b.bits he

end PositiveBinaryWord
end Blotto
