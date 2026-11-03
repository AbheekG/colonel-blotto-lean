import Blotto.BinaryWordWidth

/-! Least sufficient binary scaling from bit lengths and one shift
comparison. No full division of the input integers is performed. -/

namespace Blotto

def ratioLogDifference (a b : ℕ) : ℕ := (a - 1).log2 - b.log2

def binaryRatioPrecision (a b : ℕ) : ℕ :=
  if a ≤ b then 0 else
    let d := ratioLogDifference a b
    if a ≤ b <<< d then d else d + 1

theorem ratioLogDifference_add (a b : ℕ) (h : b < a) :
    ratioLogDifference a b + b.log2 = (a - 1).log2 := by
  have hm := binaryWordWidth_mono (show b ≤ a - 1 by omega)
  unfold binaryWordWidth at hm
  unfold ratioLogDifference
  omega

theorem ratio_upper_power (a b : ℕ) (hb : 0 < b) (h : b < a) :
    a ≤ b * 2 ^ (ratioLogDifference a b + 1) := by
  have he := ratioLogDifference_add a b h
  have hp := (Nat.le_log2 (ne_of_gt hb)).mp (Nat.le_refl b.log2)
  have hx := Nat.lt_log2_self (n := a - 1)
  have hpow : 2 ^ ((a - 1).log2 + 1) = 2 ^ b.log2 * 2 ^ (ratioLogDifference a b + 1) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hpow] at hx
  have hm := Nat.mul_le_mul_right (2 ^ (ratioLogDifference a b + 1)) hp
  omega

theorem ratio_lower_exponent (a b : ℕ) (hb : 0 < b) (h : b < a) (K : ℕ)
    (hK : a ≤ b * 2 ^ K) : ratioLogDifference a b ≤ K := by
  have he := ratioLogDifference_add a b h
  have ha : a - 1 ≠ 0 := by omega
  have hp := (Nat.le_log2 ha).mp (Nat.le_refl (a - 1).log2)
  have hu := Nat.lt_log2_self (n := b)
  by_contra hn
  have hexp : b.log2 + 1 + K ≤ (a - 1).log2 := by omega
  have hmul : b * 2 ^ K < 2 ^ (b.log2 + 1 + K) := by
    rw [pow_add]
    exact Nat.mul_lt_mul_of_pos_right hu (Nat.two_pow_pos K)
  have hpow := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hexp
  omega

theorem binaryRatioPrecision_bound (a b : ℕ) (hb : 0 < b) : a ≤ b * 2 ^ binaryRatioPrecision a b := by
  unfold binaryRatioPrecision
  split
  · simpa only [pow_zero, mul_one] using ‹a ≤ b›
  · rename_i h
    dsimp only
    split
    · simpa only [Nat.shiftLeft_eq] using ‹a ≤ b <<< ratioLogDifference a b›
    · exact ratio_upper_power a b hb (lt_of_not_ge h)

theorem binaryRatioPrecision_minimal (a b : ℕ) (hb : 0 < b) (K : ℕ)
    (hK : a ≤ b * 2 ^ K) : binaryRatioPrecision a b ≤ K := by
  unfold binaryRatioPrecision
  split
  · exact Nat.zero_le K
  · rename_i h
    dsimp only
    split
    · exact ratio_lower_exponent a b hb (lt_of_not_ge h) K hK
    · rename_i hshift
      by_contra hn
      have hk : K ≤ ratioLogDifference a b := by omega
      have hpow := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hk
      have he : a ≤ b <<< ratioLogDifference a b := by
        rw [Nat.shiftLeft_eq]
        exact hK.trans (Nat.mul_le_mul_left b hpow)
      exact hshift he

theorem ratio_shift_wordWidth (a b : ℕ) (hb : 0 < b) (h : b < a) :
    binaryWordWidth (b <<< ratioLogDifference a b) ≤ binaryWordWidth a := by
  have he := ratioLogDifference_add a b h
  have hu := Nat.lt_log2_self (n := b)
  have hx : b <<< ratioLogDifference a b < 2 ^ ((a - 1).log2 + 1) := by
    rw [Nat.shiftLeft_eq]
    have hm := Nat.mul_lt_mul_of_pos_right hu (Nat.two_pow_pos (ratioLogDifference a b))
    rw [← pow_add] at hm
    convert! hm using 1
    congr 1
    omega
  have hp : 0 < b <<< ratioLogDifference a b := by
    rw [Nat.shiftLeft_eq]
    exact Nat.mul_pos hb (Nat.two_pow_pos _)
  have hl := (Nat.log2_lt (ne_of_gt hp)).mpr hx
  have hw : binaryWordWidth (b <<< ratioLogDifference a b) ≤ binaryWordWidth (a - 1) := by
    unfold binaryWordWidth
    omega
  exact hw.trans (binaryWordWidth_mono (Nat.sub_le a 1))

end Blotto
