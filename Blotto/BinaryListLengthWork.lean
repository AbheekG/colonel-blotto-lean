import Blotto.BinaryWordWidthCore

/-! Bit-word prices for the native tail-recursive length counter. The bound
counts old/new counter words and the increment primitive at every cell. List
addressing and physical integer/allocator implementations remain separate. -/

namespace Blotto

def listLengthBitWork {α : Type*} (primitive : ℕ → ℕ) : ℕ → List α → ℕ
  | count, [] => binaryWordWidth count
  | count, _ :: rest => binaryWordWidth count + binaryWordWidth (count + 1) +
    primitive (binaryWordWidth (count + 1)) + 1 + listLengthBitWork primitive (count + 1) rest

theorem listLengthBitWork_bound {α : Type*} (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c * w) (count : ℕ) (items : List α) :
    listLengthBitWork primitive count items ≤
      (items.length + 1) * ((c + 2) * binaryWordWidth (count + items.length + 1) + 1) := by
  induction items generalizing count with
  | nil =>
    have hWidth := binaryWordWidth_mono (show count ≤ count + 0 + 1 by omega)
    simp only [listLengthBitWork, List.length_nil, Nat.zero_add, Nat.one_mul]
    nlinarith
  | cons item rest ih =>
    let W := binaryWordWidth (count + rest.length + 2)
    have hOld : binaryWordWidth count ≤ W := binaryWordWidth_mono (by omega)
    have hNew : binaryWordWidth (count + 1) ≤ W := binaryWordWidth_mono (by omega)
    have hPrimitiveBound := (hPrimitive (binaryWordWidth (count + 1))).trans (Nat.mul_le_mul_left c hNew)
    have hTail := ih (count + 1)
    have hSame : count + 1 + rest.length + 1 = count + rest.length + 2 := by omega
    rw [hSame] at hTail
    change listLengthBitWork primitive (count + 1) rest ≤ (rest.length + 1) * ((c + 2) * W + 1) at hTail
    have hGoalSame : count + (item :: rest).length + 1 = count + rest.length + 2 := by simp; omega
    rw [hGoalSame]
    change _ ≤ ((item :: rest).length + 1) * ((c + 2) * W + 1)
    simp only [listLengthBitWork, List.length_cons]
    nlinarith

end Blotto
