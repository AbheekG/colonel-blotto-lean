import Blotto.RationalExpression

/-! Fixed-depth rational programs have output bit height linear in input
height. The exponential factor concerns syntax depth, not numerical slack. -/

namespace Blotto

def expressionHeightBudget (s d : ℕ) : ℕ := (s + 1) * 2 ^ d - 1

theorem expressionHeightBudget_zero (s : ℕ) : expressionHeightBudget s 0 = s := by simp [expressionHeightBudget]

theorem expressionHeightBudget_mono (s : ℕ) {a b : ℕ} (h : a ≤ b) :
    expressionHeightBudget s a ≤ expressionHeightBudget s b :=
  Nat.sub_le_sub_right (Nat.mul_le_mul_left (s + 1) (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) h)) 1

theorem expressionHeightBudget_succ (s d : ℕ) :
    expressionHeightBudget s (d + 1) = 2 * expressionHeightBudget s d + 1 := by
  have hp : 0 < (s + 1) * 2 ^ d := Nat.mul_pos (by omega) (Nat.two_pow_pos d)
  have he : (s + 1) * 2 ^ (d + 1) = 2 * ((s + 1) * 2 ^ d) := by rw [pow_succ]; ring
  unfold expressionHeightBudget
  rw [he]
  omega

namespace RationalExpression

theorem run_height {k : ℕ} (e : RationalExpression k) (env : FixedArrayTable k ℚ) (s : ℕ)
    (hEnv : ∀ j, RationalHeight (env.read j) s) (hLit : e.LiteralHeights s) :
    RationalHeight (e.run env).1 (expressionHeightBudget s e.depth) := by
  induction e with
  | input j => simpa only [run, depth, expressionHeightBudget_zero] using hEnv j
  | literal q => simpa only [LiteralHeights, run, depth, expressionHeightBudget_zero] using hLit
  | add a b ha hb =>
    have hx := (ha hLit.1).mono (expressionHeightBudget_mono s (le_max_left a.depth b.depth))
    have hy := (hb hLit.2).mono (expressionHeightBudget_mono s (le_max_right a.depth b.depth))
    simpa only [run, depth, expressionHeightBudget_succ, two_mul] using hx.add hy
  | sub a b ha hb =>
    have hx := (ha hLit.1).mono (expressionHeightBudget_mono s (le_max_left a.depth b.depth))
    have hy := (hb hLit.2).mono (expressionHeightBudget_mono s (le_max_right a.depth b.depth))
    simpa only [run, depth, expressionHeightBudget_succ, two_mul] using hx.sub hy
  | mul a b ha hb =>
    have hx := (ha hLit.1).mono (expressionHeightBudget_mono s (le_max_left a.depth b.depth))
    have hy := (hb hLit.2).mono (expressionHeightBudget_mono s (le_max_right a.depth b.depth))
    have h := hx.mul hy
    exact h.mono (by simp only [depth, expressionHeightBudget_succ]; omega)
  | div a b ha hb =>
    have hx := (ha hLit.1).mono (expressionHeightBudget_mono s (le_max_left a.depth b.depth))
    have hy := (hb hLit.2).mono (expressionHeightBudget_mono s (le_max_right a.depth b.depth))
    rw [safe_div_value]
    exact (hx.div hy).mono (by simp only [depth, expressionHeightBudget_succ]; omega)
  | minimum a b ha hb =>
    have hx := (ha hLit.1).mono (expressionHeightBudget_mono s (le_max_left a.depth b.depth))
    have hy := (hb hLit.2).mono (expressionHeightBudget_mono s (le_max_right a.depth b.depth))
    exact (hx.min hy).mono (expressionHeightBudget_mono s (Nat.le_succ _))
  | maximum a b ha hb =>
    have hx := (ha hLit.1).mono (expressionHeightBudget_mono s (le_max_left a.depth b.depth))
    have hy := (hb hLit.2).mono (expressionHeightBudget_mono s (le_max_right a.depth b.depth))
    exact (hx.max hy).mono (expressionHeightBudget_mono s (Nat.le_succ _))
  | ifLe a b yes no _ha _hb hy hn =>
    have hDy : yes.depth ≤ max (max a.depth b.depth) (max yes.depth no.depth) + 1 := by omega
    have hDn : no.depth ≤ max (max a.depth b.depth) (max yes.depth no.depth) + 1 := by omega
    have hY := (hy hLit.2.2.1).mono (expressionHeightBudget_mono s hDy)
    have hN := (hn hLit.2.2.2).mono (expressionHeightBudget_mono s hDn)
    simp only [run, depth]
    split
    · exact hY
    · exact hN

end RationalExpression
end Blotto
