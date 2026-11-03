import Blotto.BinaryRatListDecodingCost

/-! Natural count bookkeeping for the actual short-circuit rational-row
reader. Each positive attempt prices zero testing/decrement and counter word
copies, including failed reads. Success strictly consumes frame bits, so an
enormous declared count does not cause an enormous number of attempts. -/

namespace Blotto.BinaryRatListFrame

def counterBitWork (primitive : ℕ → ℕ) : ℕ → List Bool → ℕ
  | 0, _ => binaryWordWidth 0 + primitive (binaryWordWidth 0) + 1
  | count + 1, frame =>
    4 * binaryWordWidth (count + 1) + 2 * primitive (binaryWordWidth (count + 1)) + 1 +
      match BinaryRatFrame.read frame with
      | none => 0
      | some first => counterBitWork primitive count first.2

theorem counterBitWork_bound (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c * w) (count : ℕ) (frame : List Bool) :
    counterBitWork primitive count frame ≤
      (frame.length + 1) * ((4 + 2 * c) * binaryWordWidth count + 1) := by
  induction count generalizing frame with
  | zero =>
    have hp := hPrimitive (binaryWordWidth 0)
    have hUnit : binaryWordWidth 0 + primitive (binaryWordWidth 0) + 1 ≤
        (4 + 2 * c) * binaryWordWidth 0 + 1 := by nlinarith
    have hMul := Nat.mul_le_mul_right ((4 + 2 * c) * binaryWordWidth 0 + 1) (show 1 ≤ frame.length + 1 by omega)
    simp only [Nat.one_mul] at hMul
    exact hUnit.trans hMul
  | succ count ih =>
    have hp := hPrimitive (binaryWordWidth (count + 1))
    have hWidth := binaryWordWidth_mono (show count ≤ count + 1 by omega)
    simp only [counterBitWork]
    cases hRead : BinaryRatFrame.read frame with
    | none =>
      simp only
      have hMul := Nat.mul_le_mul_right ((4 + 2 * c) * binaryWordWidth (count + 1) + 1)
        (show 1 ≤ frame.length + 1 by omega)
      simp only [Nat.one_mul] at hMul
      nlinarith
    | some first =>
      rcases first with ⟨q, suffix⟩
      have hSuffix := BinaryRatFrame.read_suffix_lt frame q suffix hRead
      have hTail := (ih suffix).trans (Nat.mul_le_mul_left (suffix.length + 1)
        (Nat.add_le_add_right (Nat.mul_le_mul_left (4 + 2 * c) hWidth) 1))
      have hMul := Nat.mul_le_mul_right ((4 + 2 * c) * binaryWordWidth (count + 1) + 1)
        (show suffix.length + 2 ≤ frame.length + 1 by omega)
      simp only
      nlinarith

end Blotto.BinaryRatListFrame
