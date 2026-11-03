import Blotto.BinaryCarryCounterSize
import Blotto.BinaryPayloadCounts

/-! Balanced assembly of the final small counter has a linear merge-size
certificate in the counted input. These are bit/block labels; integer-backend,
allocation and physical instruction costs remain separate. -/

namespace Blotto.BinaryCarryCounter

theorem square_pow_bound (w : ℕ) : w * w ≤ 4 * 2 ^ (w - 1) := by
  induction w with
  | zero => simp
  | succ w ih =>
    by_cases hSmall : w < 3
    · have hCases : w = 0 ∨ w = 1 ∨ w = 2 := by omega
      rcases hCases with rfl | rfl | rfl <;> norm_num
    · have hPos : 1 ≤ w := by omega
      have hSquare : (w + 1) * (w + 1) ≤ 2 * (w * w) := by nlinarith
      have hDouble := Nat.mul_le_mul_left 2 ih
      have hPow : 2 ^ w = 2 * 2 ^ (w - 1) := by
        conv_lhs => rw [← Nat.sub_add_cancel hPos]
        rw [pow_succ]
        ring
      simp only [Nat.add_sub_cancel]
      rw [hPow]
      nlinarith

theorem canonical_square_bound (bits : List Bool) (h : Canonical bits) :
    bits.length * bits.length ≤ 4 * value bits := by
  by_cases hn : bits = []
  · subst bits
    exact Nat.zero_le _
  · exact (square_pow_bound bits.length).trans (Nat.mul_le_mul_left 4 (value_lower bits h hn))

theorem wordWidth_double (w : ℕ) (hw : 0 < w) : binaryWordWidth w ≤ 2 * w := by
  have h := Nat.log2_le_self w
  unfold binaryWordWidth
  omega

theorem counter_mergeSize_bound {α : Type*} (items : List α) :
    BinaryPayload.mergeSize (count items [true]).length ≤ 8 * (items.length + 1) := by
  let bits := count items [true]
  have hCanon : Canonical bits := count_canonical items [true] ⟨trivial, fun _ => rfl⟩
  have hValue : value bits = items.length + 1 := by
    rw [count_value]
    change 1 + items.length = items.length + 1
    omega
  have hSq := canonical_square_bound bits hCanon
  rw [hValue] at hSq
  by_cases hn : bits.length = 0
  · change BinaryPayload.mergeSize bits.length ≤ _
    rw [hn]
    simp [BinaryPayload.mergeSize]
  · have hWidth := wordWidth_double bits.length (by omega)
    have hMerge := BinaryPayload.mergeSize_word_bound bits.length
    have hMul := Nat.mul_le_mul_left bits.length hWidth
    have hDouble := Nat.mul_le_mul_left 2 hSq
    calc
      BinaryPayload.mergeSize bits.length ≤ bits.length * binaryWordWidth bits.length := hMerge
      _ ≤ 2 * (bits.length * bits.length) := by nlinarith [hMul]
      _ ≤ 8 * (items.length + 1) := by nlinarith [hDouble]

end Blotto.BinaryCarryCounter
