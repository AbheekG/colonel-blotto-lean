import Blotto.RationalExpressionHeight

/-! The expression bit-height certificate bounds the actual reduced
numerator/denominator word lengths used by the native rational backend. -/

namespace Blotto

theorem binaryWordWidth_le_of_lt_pow {n s : ℕ} (hs : 0 < s) (h : n < 2 ^ s) : binaryWordWidth n ≤ s := by
  by_cases hn : n = 0
  · simp only [hn, binaryWordWidth, Nat.log2_zero]
    omega
  · have hl := (Nat.log2_lt hn).mpr h
    unfold binaryWordWidth
    omega

theorem rationalHeight_of_wordWidth (q : ℚ) : RationalHeight q (rationalWordWidth q) := by
  have hN := lt_pow_binaryWordWidth q.num.natAbs
  have hD := lt_pow_binaryWordWidth q.den
  have hn : binaryWordWidth q.num.natAbs ≤ rationalWordWidth q := by unfold rationalWordWidth; omega
  have hd : binaryWordWidth q.den ≤ rationalWordWidth q := by unfold rationalWordWidth; omega
  exact ⟨hN.trans_le (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hn),
    hD.trans_le (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hd)⟩

theorem rationalWordWidth_of_height {q : ℚ} {s : ℕ} (h : RationalHeight q s) : rationalWordWidth q ≤ 1 + 2 * s := by
  have hn := binaryWordWidth_le_of_lt_pow h.positive h.1
  have hd := binaryWordWidth_le_of_lt_pow h.positive h.2
  unfold rationalWordWidth
  omega

namespace RationalExpression

theorem run_wordWidth {k : ℕ} (e : RationalExpression k) (env : FixedArrayTable k ℚ) (s : ℕ)
    (hEnv : ∀ j, RationalHeight (env.read j) s) (hLit : e.LiteralHeights s) :
    rationalWordWidth (e.run env).1 ≤ 1 + 2 * expressionHeightBudget s e.depth :=
  rationalWordWidth_of_height (e.run_height env s hEnv hLit)

end RationalExpression
end Blotto
