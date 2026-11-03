import Blotto.BinaryRatioPrecision

/-! Least ratio precision can be selected from the two positive word widths
and one aligned comparison. This numerical specification is the bridge for
the direct bit-word accuracy algorithm. -/

namespace Blotto

def widthRatioCandidate (a b : ℕ) : ℕ := binaryWordWidth a - binaryWordWidth b

def widthRatioPrecision (a b : ℕ) : ℕ :=
  let c := widthRatioCandidate a b
  if a ≤ b <<< c then c else c + 1

theorem widthRatioCandidate_log (a b : ℕ) : widthRatioCandidate a b = a.log2 - b.log2 := by
  unfold widthRatioCandidate binaryWordWidth
  omega

theorem widthRatio_upper (a b : ℕ) (hb : 0 < b) : a ≤ b * 2 ^ (widthRatioCandidate a b + 1) := by
  have hl := (Nat.le_log2 (ne_of_gt hb)).mp (Nat.le_refl b.log2)
  have hu := Nat.lt_log2_self (n := a)
  have he : a.log2 + 1 ≤ b.log2 + (widthRatioCandidate a b + 1) := by rw [widthRatioCandidate_log]; omega
  have hp := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) he
  have hm := Nat.mul_le_mul_right (2 ^ (widthRatioCandidate a b + 1)) hl
  rw [← pow_add] at hm
  omega

theorem widthRatio_lower (a b K : ℕ) (ha : 0 < a) (_hb : 0 < b) (hK : a ≤ b * 2 ^ K) :
    widthRatioCandidate a b ≤ K := by
  have hl := (Nat.le_log2 (ne_of_gt ha)).mp (Nat.le_refl a.log2)
  have hu := Nat.lt_log2_self (n := b)
  by_contra h
  have he : b.log2 + 1 + K ≤ a.log2 := by rw [widthRatioCandidate_log] at h; omega
  have hm := Nat.mul_lt_mul_of_pos_right hu (Nat.two_pow_pos K)
  rw [← pow_add] at hm
  have hp := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) he
  omega

theorem widthRatioPrecision_bound (a b : ℕ) (hb : 0 < b) : a ≤ b * 2 ^ widthRatioPrecision a b := by
  unfold widthRatioPrecision
  dsimp only
  split
  · simpa only [Nat.shiftLeft_eq] using ‹a ≤ b <<< widthRatioCandidate a b›
  · exact widthRatio_upper a b hb

theorem widthRatioPrecision_minimal (a b K : ℕ) (ha : 0 < a) (hb : 0 < b) (hK : a ≤ b * 2 ^ K) :
    widthRatioPrecision a b ≤ K := by
  have hc := widthRatio_lower a b K ha hb hK
  unfold widthRatioPrecision
  dsimp only
  split
  · exact hc
  · rename_i hFail
    by_contra h
    have he : K = widthRatioCandidate a b := by omega
    apply hFail
    simpa only [Nat.shiftLeft_eq, he] using hK

theorem widthRatioPrecision_eq (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    widthRatioPrecision a b = binaryRatioPrecision a b := by
  apply Nat.le_antisymm
  · exact widthRatioPrecision_minimal a b _ ha hb (binaryRatioPrecision_bound a b hb)
  · exact binaryRatioPrecision_minimal a b hb _ (widthRatioPrecision_bound a b hb)

theorem binaryWordWidth_shift (n shift : ℕ) (hn : 0 < n) : binaryWordWidth (n <<< shift) = binaryWordWidth n + shift := by
  have hl := (Nat.le_log2 (ne_of_gt hn)).mp (Nat.le_refl n.log2)
  have hu := Nat.lt_log2_self (n := n)
  have hp : 0 < n <<< shift := by rw [Nat.shiftLeft_eq]; exact Nat.mul_pos hn (Nat.two_pow_pos shift)
  have hLow : 2 ^ (n.log2 + shift) ≤ n <<< shift := by
    rw [Nat.shiftLeft_eq, pow_add]
    exact Nat.mul_le_mul_right _ hl
  have hHigh : n <<< shift < 2 ^ (n.log2 + shift + 1) := by
    rw [Nat.shiftLeft_eq]
    have h := Nat.mul_lt_mul_of_pos_right hu (Nat.two_pow_pos shift)
    rw [← pow_add] at h
    convert h using 1
    congr 1
    omega
  have hLe := (Nat.le_log2 (ne_of_gt hp)).mpr hLow
  have hLt := (Nat.log2_lt (ne_of_gt hp)).mpr hHigh
  unfold binaryWordWidth
  omega

end Blotto
