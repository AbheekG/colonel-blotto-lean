import Blotto.RationalPreparationCommonPrice

/-! Available comparison operands pay their words and a rational primitive.
The physical comparison implementation remains a separate model contract. -/

namespace Blotto.RationalPreparationComparison

def bitCost (model : RationalCostModel) (a b : ℚ) : ℕ :=
  rationalWordWidth a + rationalWordWidth b + model.rat (RationalExpression.pairWidth a b)

theorem bitCost_bound (model : RationalCostModel) (a b : ℚ) (s : ℕ)
    (ha : RationalHeight a s) (hb : RationalHeight b s) :
    bitCost model a b ≤ 3 * model.rat (1 + 2 * s) := by
  have hA := (rationalWordWidth_of_height ha).trans (model.word_le _)
  have hB := (rationalWordWidth_of_height hb).trans (model.word_le _)
  have hp := model.monotone (RationalExpression.pairWidth_height ha hb)
  unfold bitCost
  omega

end Blotto.RationalPreparationComparison
