import Blotto.OverlapFormulaCode
import Blotto.RationalExpressionIntermediates
import Blotto.RationalExpressionLiteralHeight

/-! Fixed expression depth/literal certificates for all overlap operands.
Safe endpoints include both the budget row and the active inverse formulas. -/

namespace Blotto.OverlapFormulaCode

theorem weight_depth : weight.depth ≤ 7 := by decide
theorem safeP_depth (r : Fin 4) : (safeP r).depth ≤ 9 := by fin_cases r <;> decide
theorem safeQ_depth (r : Fin 4) : (safeQ r).depth ≤ 9 := by fin_cases r <;> decide

theorem weight_literals : weight.LiteralHeights 2 := by
  norm_num [weight, lower, upper, absolute, reflectedP, reflectedQ, firstP, firstQ,
    secondP, secondQ, intervalLength, firstWeight, secondWeight,
    RationalExpression.LiteralHeights, RationalHeight]

theorem safeP_literals (r : Fin 4) : (safeP r).LiteralHeights 2 := by
  fin_cases r <;> norm_num [safeP, fallback, curve, interpolate, firstInverse, secondInverse,
    weight, lower, upper, absolute, reflectedP, reflectedQ, firstP, firstQ, secondP, secondQ,
    intervalLength, firstWeight, secondWeight, budget, RationalExpression.LiteralHeights, RationalHeight]

theorem safeQ_literals (r : Fin 4) : (safeQ r).LiteralHeights 2 := by
  fin_cases r <;> norm_num [safeQ, fallback, curve, interpolate, firstInverse, secondInverse,
    weight, lower, upper, absolute, reflectedP, reflectedQ, firstP, firstQ, secondP, secondQ,
    intervalLength, firstWeight, secondWeight, budget, RationalExpression.LiteralHeights, RationalHeight]

theorem weight_intermediates (env : FixedArrayTable 16 ℚ) (s : ℕ) (hs : 2 ≤ s)
    (hEnv : ∀ j, RationalHeight (env.read j) s) :
    weight.AllRunHeights env (expressionHeightBudget s 7) := by
  have h := weight.run_all_heights env s hEnv (weight.LiteralHeights_mono hs weight_literals)
  exact RationalExpression.AllRunHeights_mono _ _ (expressionHeightBudget_mono s weight_depth) h

theorem safeP_intermediates (r : Fin 4) (env : FixedArrayTable 16 ℚ) (s : ℕ) (hs : 2 ≤ s)
    (hEnv : ∀ j, RationalHeight (env.read j) s) :
    (safeP r).AllRunHeights env (expressionHeightBudget s 9) := by
  have h := (safeP r).run_all_heights env s hEnv ((safeP r).LiteralHeights_mono hs (safeP_literals r))
  exact RationalExpression.AllRunHeights_mono _ _ (expressionHeightBudget_mono s (safeP_depth r)) h

theorem safeQ_intermediates (r : Fin 4) (env : FixedArrayTable 16 ℚ) (s : ℕ) (hs : 2 ≤ s)
    (hEnv : ∀ j, RationalHeight (env.read j) s) :
    (safeQ r).AllRunHeights env (expressionHeightBudget s 9) := by
  have h := (safeQ r).run_all_heights env s hEnv ((safeQ r).LiteralHeights_mono hs (safeQ_literals r))
  exact RationalExpression.AllRunHeights_mono _ _ (expressionHeightBudget_mono s (safeQ_depth r)) h

end Blotto.OverlapFormulaCode
