import Blotto.RationalExpressionValue

/-! Literal certificates can be raised to a common input height without
changing the arithmetic program. -/

namespace Blotto.RationalExpression

theorem LiteralHeights_mono {k s t : ℕ} (e : RationalExpression k) (hst : s ≤ t)
    (h : e.LiteralHeights s) : e.LiteralHeights t := by
  induction e with
  | input j => trivial
  | literal q => exact h.mono hst
  | add a b ha hb => exact ⟨ha h.1, hb h.2⟩
  | sub a b ha hb => exact ⟨ha h.1, hb h.2⟩
  | mul a b ha hb => exact ⟨ha h.1, hb h.2⟩
  | div a b ha hb => exact ⟨ha h.1, hb h.2⟩
  | minimum a b ha hb => exact ⟨ha h.1, hb h.2⟩
  | maximum a b ha hb => exact ⟨ha h.1, hb h.2⟩
  | ifLe a b yes no ha hb hy hn => exact ⟨ha h.1, hb h.2.1, hy h.2.2.1, hn h.2.2.2⟩

end Blotto.RationalExpression
