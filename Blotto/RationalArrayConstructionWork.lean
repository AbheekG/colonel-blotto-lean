import Blotto.RationalExpressionWordWidth

/-! Conservative rational payload copying for sequential array construction.
Every push may copy the complete old prefix and the new word. This does not
assume exclusivity or amortized resizing; physical addresses/allocator records
are separate from these payload-word copies. -/

namespace Blotto

def rationalArrayCopyWork : List ℚ → ℕ → ℕ
  | [], _ => 0
  | q :: rest, prefixWords =>
    2 * (prefixWords + rationalWordWidth q) + rationalArrayCopyWork rest (prefixWords + rationalWordWidth q)

theorem rationalArrayCopyWork_bound (row : List ℚ) (prefixWords : ℕ) :
    rationalArrayCopyWork row prefixWords ≤ 2 * row.length * (prefixWords + (row.map rationalWordWidth).sum) := by
  induction row generalizing prefixWords with
  | nil => simp [rationalArrayCopyWork]
  | cons q rest ih =>
    have ht := ih (prefixWords + rationalWordWidth q)
    simp only [rationalArrayCopyWork, List.length_cons, List.map_cons, List.sum_cons]
    calc
      _ ≤ 2 * (prefixWords + rationalWordWidth q) +
          2 * rest.length * (prefixWords + rationalWordWidth q + (rest.map rationalWordWidth).sum) := Nat.add_le_add_left ht _
      _ ≤ 2 * (prefixWords + rationalWordWidth q + (rest.map rationalWordWidth).sum) +
          2 * rest.length * (prefixWords + rationalWordWidth q + (rest.map rationalWordWidth).sum) :=
        Nat.add_le_add_right (Nat.mul_le_mul_left 2 (by omega)) _
      _ = _ := by ring

theorem rationalWordWidth_sum_bound (row : List ℚ) (W : ℕ)
    (h : ∀ q ∈ row, rationalWordWidth q ≤ W) : (row.map rationalWordWidth).sum ≤ row.length * W := by
  induction row with
  | nil => simp
  | cons q rest ih =>
    have hq := h q (by simp)
    have hr := ih (fun x hx => h x (by simp [hx]))
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    nlinarith

end Blotto
