import Blotto.RationalFractionalTest
import Blotto.RationalExpressionBitCost

/-! Selected-branch operand prices for the cached source fractional test.
Reader execution and address/control/container work remain separate. -/

namespace Blotto

def rationalFractionalBitCost {α : Type*} (model : RationalCostModel) (L r : α → ℚ) (j : α) : ℕ :=
  rationalWordWidth (r j) + model.rat (RationalExpression.pairWidth 0 (r j)) +
    if 0 < r j then rationalWordWidth (r j) + rationalWordWidth (L j) +
      model.rat (RationalExpression.pairWidth (r j) (L j)) else 0


theorem rationalFractionalBitCost_bound {α : Type*} (model : RationalCostModel) (L r : α → ℚ) (j : α) (W : ℕ)
    (hZero : rationalWordWidth (0 : ℚ) ≤ W) (hL : rationalWordWidth (L j) ≤ W)
    (hR : rationalWordWidth (r j) ≤ W) : rationalFractionalBitCost model L r j ≤ 5 * model.rat W := by
  have hRead := hR.trans (model.word_le W)
  have hCap := hL.trans (model.word_le W)
  have hPositive := model.monotone (show RationalExpression.pairWidth 0 (r j) ≤ W from max_le hZero hR)
  have hUpper := model.monotone (show RationalExpression.pairWidth (r j) (L j) ≤ W from max_le hR hL)
  unfold rationalFractionalBitCost
  split_ifs <;> omega

end Blotto
