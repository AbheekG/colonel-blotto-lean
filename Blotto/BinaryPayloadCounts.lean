import Blotto.BinaryPayload

/-! Balanced payload decoding reads each leaf bit once. The sum of block
lengths charged to shift/add merges is at most w times its binary word width.
These labels exclude integer-backend and container-allocation costs. -/

namespace Blotto.BinaryPayload

def readCount (length : ℕ) : ℕ :=
  if length = 0 then 0 else if length = 1 then 1 else readCount (length / 2) + readCount (length - length / 2)
termination_by length
decreasing_by all_goals omega

theorem readCount_eq (length : ℕ) : readCount length = length := by
  unfold readCount
  split
  · rename_i h; omega
  · split
    · rename_i h; omega
    · rw [readCount_eq, readCount_eq]
      omega
termination_by length
decreasing_by all_goals omega

def mergeCount (length : ℕ) : ℕ :=
  if length ≤ 1 then 0 else mergeCount (length / 2) + mergeCount (length - length / 2) + 1
termination_by length
decreasing_by all_goals omega

theorem mergeCount_eq (length : ℕ) : mergeCount length = length - 1 := by
  unfold mergeCount
  split
  · rename_i h; omega
  · rw [mergeCount_eq, mergeCount_eq]
    omega
termination_by length
decreasing_by all_goals omega

def mergeSize (length : ℕ) : ℕ :=
  if length ≤ 1 then 0 else mergeSize (length / 2) + mergeSize (length - length / 2) + length
termination_by length
decreasing_by all_goals omega

theorem mergeSize_pow_bound (depth length : ℕ) (h : length ≤ 2 ^ depth) : mergeSize length ≤ length * depth := by
  induction depth generalizing length with
  | zero =>
    have hl : length ≤ 1 := by simpa using h
    rw [mergeSize, ite_eq_left hl]
    simp
  | succ depth ih =>
    by_cases hl : length ≤ 1
    · rw [mergeSize, ite_eq_left hl]
      exact Nat.zero_le _
    · have hp : length ≤ 2 * 2 ^ depth := by simpa only [pow_succ, Nat.mul_comm] using h
      have hLow : length / 2 ≤ 2 ^ depth := by omega
      have hHigh : length - length / 2 ≤ 2 ^ depth := by omega
      have lo := ih _ hLow
      have hi := ih _ hHigh
      rw [mergeSize, ite_eq_right hl]
      calc
        mergeSize (length / 2) + mergeSize (length - length / 2) + length ≤
            length / 2 * depth + (length - length / 2) * depth + length :=
          Nat.add_le_add_right (Nat.add_le_add lo hi) length
        _ = length * (depth + 1) := by
          rw [← Nat.add_mul, show length / 2 + (length - length / 2) = length by omega]
          ring

theorem mergeSize_word_bound (length : ℕ) : mergeSize length ≤ length * binaryWordWidth length :=
  mergeSize_pow_bound _ _ (Nat.le_of_lt (lt_pow_binaryWordWidth length))

end Blotto.BinaryPayload
