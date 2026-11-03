import Blotto.BinaryCoinWordStep

/-! A width-indexed Boolean word gives subtraction/coin routines their exact
length invariant. Leading zeros and the zero word remain valid representations. -/

namespace Blotto

structure FixedBinaryWord (width : ℕ) where
  bits : List Bool
  size : bits.length = width

namespace FixedBinaryWord

def value {w : ℕ} (a : FixedBinaryWord w) : ℕ := BinaryBigEndian.littleValue a.bits

def ofNat (w n : ℕ) : FixedBinaryWord w := ⟨BinaryPayload.bits w n, BinaryPayload.bits_length w n⟩

theorem value_ofNat (w n : ℕ) (h : n < 2 ^ w) : (ofNat w n).value = n := by
  unfold value ofNat
  rw [BinaryBigEndian.littleValue_decode, BinaryPayload.decode_bits w n h]

def sameScan : List Bool → List Bool → Bool
  | [], [] => true
  | a :: as, b :: bs => if a = b then sameScan as bs else false
  | _, _ => false

theorem sameScan_eq (a b : List Bool) : sameScan a b = true ↔ a = b := by
  induction a generalizing b with
  | nil => cases b <;> simp [sameScan]
  | cons bit rest ih =>
    cases b with
    | nil => simp [sameScan]
    | cons other tail =>
      by_cases h : bit = other
      · subst other; simpa [sameScan] using ih tail
      · simp [sameScan, h]

def same {w : ℕ} (a b : FixedBinaryWord w) : Bool := sameScan a.bits b.bits

theorem same_value {w : ℕ} (a b : FixedBinaryWord w) : a.same b = true ↔ a.value = b.value := by
  rw [same, sameScan_eq]
  constructor
  · intro h; simp only [value, h]
  · intro h
    exact BinaryBorrowWord.littleValue_injective a.bits b.bits (a.size.trans b.size.symm) h

def isZero {w : ℕ} (a : FixedBinaryWord w) : Bool := a.bits.all (fun b => !b)

theorem all_false_value (bits : List Bool) : bits.all (fun b => !b) = true ↔ BinaryBigEndian.littleValue bits = 0 := by
  induction bits with
  | nil => simp [BinaryBigEndian.littleValue]
  | cons bit rest ih =>
    cases bit
    · simpa [BinaryBigEndian.littleValue] using ih
    · simp [BinaryBigEndian.littleValue]

theorem isZero_value {w : ℕ} (a : FixedBinaryWord w) : a.isZero = true ↔ a.value = 0 := all_false_value a.bits

def zeroVisits : List Bool → ℕ
  | [] => 1
  | b :: rest => if b then 1 else 1 + zeroVisits rest

theorem zeroVisits_bound (bits : List Bool) : zeroVisits bits ≤ bits.length + 1 := by
  induction bits with
  | nil => rfl
  | cons b rest ih => cases b <;> simp only [zeroVisits, Bool.false_eq_true, ite_false, ite_true, List.length_cons] <;> omega

def sameVisits : List Bool → List Bool → ℕ
  | a :: as, b :: bs => if a = b then 1 + sameVisits as bs else 1
  | _, _ => 1

theorem sameVisits_bound (a b : List Bool) : sameVisits a b ≤ a.length + 1 := by
  induction a generalizing b with
  | nil => cases b <;> rfl
  | cons bit rest ih =>
    cases b with
    | nil => simp [sameVisits]
    | cons other tail =>
      have h := ih tail
      simp only [sameVisits, List.length_cons]
      split <;> omega

def coinStep {w : ℕ} (a b : FixedBinaryWord w) : Bool × FixedBinaryWord w :=
  let result := BinaryCoinWord.step a.bits b.bits
  (result.1, ⟨result.2, (BinaryCoinWord.step_length a.bits b.bits (a.size.trans b.size.symm)).trans a.size⟩)

theorem coinStep_digit {w : ℕ} (a b : FixedBinaryWord w) : (a.coinStep b).1 = denominatorDigit a.value b.value :=
  BinaryCoinWord.step_digit a.bits b.bits (a.size.trans b.size.symm)

theorem coinStep_residual {w : ℕ} (a b : FixedBinaryWord w) (h : a.value < b.value) :
    (a.coinStep b).2.value = numeratorResidual a.value b.value :=
  BinaryCoinWord.step_residual a.bits b.bits (a.size.trans b.size.symm) h

theorem coinStep_normalized {w : ℕ} (a b : FixedBinaryWord w) (h : a.value < b.value) :
    (a.coinStep b).2.value < b.value :=
  BinaryCoinWord.step_normalized a.bits b.bits (a.size.trans b.size.symm) h

end FixedBinaryWord
end Blotto
