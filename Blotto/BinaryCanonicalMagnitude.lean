import Blotto.BinaryRationalArithmetic

/-! Canonical Boolean magnitudes discard high zero bits. The runtime reverses,
scans leading false bits and reverses back, without inspecting numeric values.
Zero is represented by the empty list. Output width is bounded by the actual
represented value's binary word width; trimming has linear cell/Boolean work. -/

namespace Blotto.BinaryCanonicalMagnitude

def trim (bits : List Bool) : List Bool := (BinaryBigEndian.trim bits.reverse).reverse

theorem trim_value (bits : List Bool) : BinaryBigEndian.littleValue (trim bits) = BinaryBigEndian.littleValue bits := by
  rw [trim, ← BinaryBigEndian.value_reverse, List.reverse_reverse, BinaryBigEndian.value_trim,
    BinaryBigEndian.value_reverse]

theorem trim_length (bits : List Bool) : (trim bits).length ≤ bits.length := by
  simpa only [trim, List.length_reverse] using BinaryBigEndian.trim_length bits.reverse

theorem bigTrim_head (bits : List Bool) :
    BinaryBigEndian.trim bits = [] ∨ ∃ rest, BinaryBigEndian.trim bits = true :: rest := by
  induction bits with
  | nil => exact Or.inl rfl
  | cons bit rest ih =>
      cases bit
      · simpa only [BinaryBigEndian.trim, List.dropWhile_cons, Bool.not_false, ite_true] using ih
      · exact Or.inr ⟨rest, by simp [BinaryBigEndian.trim]⟩

theorem bigCanonical_length (bits : List Bool)
    (h : bits = [] ∨ ∃ rest, bits = true :: rest) : bits.length ≤ binaryWordWidth (BinaryBigEndian.value bits) := by
  rcases h with rfl | ⟨rest, rfl⟩
  · exact Nat.zero_le _
  · have hLow : 2 ^ rest.length ≤ BinaryBigEndian.value (true :: rest) := by
      simp only [BinaryBigEndian.value, ite_true]
      omega
    have hPos : BinaryBigEndian.value (true :: rest) ≠ 0 := by
      have hp := Nat.two_pow_pos rest.length
      omega
    have hLog := (Nat.le_log2 hPos).mpr hLow
    unfold binaryWordWidth
    simp only [List.length_cons]
    omega

theorem trim_wordWidth (bits : List Bool) : (trim bits).length ≤ binaryWordWidth (BinaryBigEndian.littleValue bits) := by
  have h := bigCanonical_length (BinaryBigEndian.trim bits.reverse) (bigTrim_head bits.reverse)
  simpa only [trim, List.length_reverse, BinaryBigEndian.value_trim, BinaryBigEndian.value_reverse] using h

theorem trim_zero (bits : List Bool) (h : BinaryBigEndian.littleValue bits = 0) : trim bits = [] := by
  rcases bigTrim_head bits.reverse with hz | ⟨rest, he⟩
  · simp only [trim, hz, List.reverse_nil]
  · have hv := BinaryBigEndian.value_trim bits.reverse
    rw [he, BinaryBigEndian.value_reverse, h] at hv
    have hp := Nat.two_pow_pos rest.length
    simp only [BinaryBigEndian.value, ite_true] at hv
    omega

def scanVisits : List Bool → ℕ
  | [] => 1
  | bit :: rest => if bit then 1 else 1 + scanVisits rest

theorem scanVisits_bound (bits : List Bool) : scanVisits bits ≤ bits.length + 1 := by
  induction bits with
  | nil => rfl
  | cons bit rest ih => cases bit <;> simp only [scanVisits, Bool.false_eq_true, ite_false, ite_true, List.length_cons] <;> omega

def bitWork (bits : List Bool) : ℕ :=
  2 * bits.length + 3 * scanVisits bits.reverse + 2 * (BinaryBigEndian.trim bits.reverse).length + 2

theorem bitWork_bound (bits : List Bool) : bitWork bits ≤ 7 * bits.length + 5 := by
  have hs := scanVisits_bound bits.reverse
  have ht := BinaryBigEndian.trim_length bits.reverse
  rw [List.length_reverse] at hs ht
  unfold bitWork
  omega

def trimWithWork (bits : List Bool) : List Bool × ℕ := (trim bits, bitWork bits)

theorem trimWithWork_contract (bits : List Bool) :
    BinaryBigEndian.littleValue (trimWithWork bits).1 = BinaryBigEndian.littleValue bits ∧
      (trimWithWork bits).1.length ≤ binaryWordWidth (BinaryBigEndian.littleValue bits) ∧
      (trimWithWork bits).2 ≤ 7 * bits.length + 5 :=
  ⟨trim_value bits, trim_wordWidth bits, bitWork_bound bits⟩

end Blotto.BinaryCanonicalMagnitude
