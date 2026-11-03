import Blotto.Rounding

/-! A conservative binary word width counts one digit even at zero.
Product-denominator widths are bounded by the sum of input widths. -/

namespace Blotto
open scoped BigOperators

def binaryWordWidth (n : ℕ) : ℕ := n.log2 + 1

theorem binaryWordWidth_pos (n : ℕ) : 0 < binaryWordWidth n := by unfold binaryWordWidth; omega

theorem lt_pow_binaryWordWidth (n : ℕ) : n < 2 ^ binaryWordWidth n := Nat.lt_log2_self

theorem binaryWordWidth_mono {m n : ℕ} (h : m ≤ n) : binaryWordWidth m ≤ binaryWordWidth n := by
  by_cases hm : m = 0
  · simp [binaryWordWidth, hm]
  · have hp : m < 2 ^ (n.log2 + 1) := h.trans_lt (Nat.lt_log2_self (n := n))
    have hl := (Nat.log2_lt hm).mpr hp
    unfold binaryWordWidth
    omega

theorem binaryWordWidth_mul (m n : ℕ) : binaryWordWidth (m * n) ≤ binaryWordWidth m + binaryWordWidth n := by
  have hm := lt_pow_binaryWordWidth m
  have hn := lt_pow_binaryWordWidth n
  have hp : m * n < 2 ^ (binaryWordWidth m + binaryWordWidth n) := by
    rw [pow_add]
    nlinarith
  by_cases hz : m * n = 0
  · simp only [hz, binaryWordWidth, Nat.log2_zero]
    have hwm := binaryWordWidth_pos m
    have hwn := binaryWordWidth_pos n
    unfold binaryWordWidth at hwm hwn
    omega
  · have he := (Nat.log2_lt hz).mpr hp
    unfold binaryWordWidth at he ⊢
    omega

theorem binaryWordWidth_finset_prod {α : Type*} (f : α → ℕ) (s : Finset α) :
    binaryWordWidth (∏ j ∈ s, f j) ≤ 1 + ∑ j ∈ s, binaryWordWidth (f j) := by
  classical
  induction s using Finset.induction_on with
  | empty => norm_num [binaryWordWidth]; decide
  | @insert x s hx ih =>
    rw [Finset.prod_insert hx, Finset.sum_insert hx]
    have he := binaryWordWidth_mul (f x) (∏ j ∈ s, f j)
    omega

def rationalWordWidth (q : ℚ) : ℕ := 1 + binaryWordWidth q.num.natAbs + binaryWordWidth q.den

end Blotto
