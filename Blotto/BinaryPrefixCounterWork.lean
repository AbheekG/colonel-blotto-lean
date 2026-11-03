import Blotto.BinaryListLengthWork

/-! Integer-word costs for take/drop-style prefix traversal. The loop stops
at zero or an empty input and prices counter tests/decrements and copies.
Cons-cell/address/physical allocation costs are separate. -/

namespace Blotto

def prefixCounterBitWork {α : Type*} (primitive : ℕ → ℕ) : ℕ → List α → ℕ
  | 0, _ => binaryWordWidth 0 + primitive (binaryWordWidth 0) + 1
  | count + 1, items => 4 * binaryWordWidth (count + 1) + 2 * primitive (binaryWordWidth (count + 1)) + 1 +
      match items with
      | [] => 0
      | _ :: rest => prefixCounterBitWork primitive count rest

theorem prefixCounterBitWork_bound {α : Type*} (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c * w) (count : ℕ) (items : List α) :
    prefixCounterBitWork primitive count items ≤ (items.length + 1) * ((4 + 2 * c) * binaryWordWidth count + 1) := by
  induction count generalizing items with
  | zero =>
    have hp := hPrimitive (binaryWordWidth 0)
    have hUnit : binaryWordWidth 0 + primitive (binaryWordWidth 0) + 1 ≤ (4 + 2 * c) * binaryWordWidth 0 + 1 := by nlinarith
    have hMul := Nat.mul_le_mul_right ((4 + 2 * c) * binaryWordWidth 0 + 1) (show 1 ≤ items.length + 1 by omega)
    simp only [Nat.one_mul] at hMul
    exact hUnit.trans hMul
  | succ count ih =>
    have hp := hPrimitive (binaryWordWidth (count + 1))
    cases items with
    | nil => simp only [prefixCounterBitWork, List.length_nil, Nat.zero_add, Nat.one_mul]; nlinarith
    | cons item rest =>
      have hWidth := binaryWordWidth_mono (show count ≤ count + 1 by omega)
      have hTail := (ih rest).trans (Nat.mul_le_mul_left (rest.length + 1)
        (Nat.add_le_add_right (Nat.mul_le_mul_left (4 + 2 * c) hWidth) 1))
      simp only [prefixCounterBitWork, List.length_cons]
      nlinarith

end Blotto
