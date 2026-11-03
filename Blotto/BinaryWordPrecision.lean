import Blotto.PositiveBinaryWordParse

/-! The precision selector aligns and compares positive Boolean words.
Large integer values appear only in the correspondence theorem. -/

namespace Blotto.PositiveBinaryWord

theorem le_decide (a b : PositiveBinaryWord) : a.le b = decide (a.value ≤ b.value) := by
  have h := le_eq a b
  cases hBit : a.le b <;> simp_all

theorem leNumeric_decide (a b : PositiveBinaryWord) : a.leNumeric b = decide (a.value ≤ b.value) := by
  rw [← le_refines]
  exact le_decide a b

def ratioPrecisionNumeric (a b : PositiveBinaryWord) : ℕ :=
  let candidate := a.width - b.width
  if a.leNumeric (b.shifted candidate) then candidate else candidate + 1

def ratioPrecision (a b : PositiveBinaryWord) : ℕ :=
  let aw := a.countedWidth
  let bw := b.countedWidth
  let candidate := aw - bw
  if a.le (b.shifted candidate) then candidate else candidate + 1

theorem ratioPrecision_refines (a b : PositiveBinaryWord) : a.ratioPrecision b = a.ratioPrecisionNumeric b := by
  simp only [ratioPrecision, countedWidth_eq, le_refines]
  rfl

theorem ratioPrecision_eq (a b : PositiveBinaryWord) : ratioPrecision a b = binaryRatioPrecision a.value b.value := by
  rw [ratioPrecision_refines]
  rw [← widthRatioPrecision_eq a.value b.value a.value_pos b.value_pos]
  simp only [ratioPrecisionNumeric, widthRatioPrecision, widthRatioCandidate, a.width_eq, b.width_eq,
    leNumeric_decide, value_shifted, decide_eq_true_eq]
  rfl

theorem aligned_width (a b : PositiveBinaryWord) : (b.shifted (a.width - b.width)).width ≤ a.width + b.width := by
  rw [width_shifted]
  omega

def leScanVisits : List Bool → List Bool → ℕ
  | [], _ => 0
  | _ :: _, [] => 0
  | a :: as, b :: bs => 1 + if a = b then leScanVisits as bs else 0

theorem leScanVisits_bound (a b : List Bool) : leScanVisits a b ≤ a.length ∧ leScanVisits a b ≤ b.length := by
  induction a generalizing b with
  | nil => simp [leScanVisits]
  | cons bit as ih =>
    cases b with
    | nil => simp [leScanVisits]
    | cons other bs =>
      have ht := ih bs
      simp only [leScanVisits, List.length_cons]
      split <;> constructor <;> omega

def leVisits (a b : PositiveBinaryWord) : ℕ :=
  if a.width < b.width then 0 else if b.width < a.width then 0 else leScanVisits a.bits b.bits

theorem leVisits_bound (a b : PositiveBinaryWord) : leVisits a b ≤ a.width := by
  unfold leVisits
  split
  · exact Nat.zero_le _
  · split
    · exact Nat.zero_le _
    · exact (leScanVisits_bound a.bits b.bits).1

def ratioTraversalWork (a b : PositiveBinaryWord) : ℕ :=
  let candidate := a.width - b.width
  let shifted := b.shifted candidate
  a.width + b.width + shifted.width + a.width + shifted.width + a.leVisits shifted

theorem ratioTraversalWork_bound (a b : PositiveBinaryWord) : ratioTraversalWork a b ≤ 5 * (a.width + b.width) := by
  have hv := leVisits_bound a (b.shifted (a.width - b.width))
  unfold ratioTraversalWork
  dsimp only
  rw [width_shifted]
  omega

end Blotto.PositiveBinaryWord
