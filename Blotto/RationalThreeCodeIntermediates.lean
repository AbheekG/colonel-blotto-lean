import Blotto.RationalThreeCodeBounds
import Blotto.RationalExpressionIntermediates

/-! All argument and comparison intermediates of the actual selected weight
and vertex programs share the same fixed-depth bit-height certificates. -/

namespace Blotto.RationalThreeGeometryCode

theorem chosen_intermediates (g : RationalThreeGeometry) (slot : Fin 9) (s : ℕ) (hs : 2 ≤ s)
    (hEnv : ∀ j, RationalHeight ((environment g).read j) s) :
    (chosen slot).AllRunHeights (environment g) (expressionHeightBudget s 16) := by
  have h := (chosen slot).run_all_heights (environment g) s hEnv
    ((chosen slot).LiteralHeights_mono hs (chosen_literals slot))
  exact RationalExpression.AllRunHeights_mono _ _ (expressionHeightBudget_mono s (chosen_depth slot)) h

theorem vertex_intermediates (g : RationalThreeGeometry) (i : Fin 6) (j : Fin 3) (s : ℕ) (hs : 2 ≤ s)
    (hEnv : ∀ j, RationalHeight ((environment g).read j) s) :
    (vertex i j).AllRunHeights (environment g) (expressionHeightBudget s 2) := by
  have h := (vertex i j).run_all_heights (environment g) s hEnv
    ((vertex i j).LiteralHeights_mono hs (vertex_literals i j))
  exact RationalExpression.AllRunHeights_mono _ _ (expressionHeightBudget_mono s (vertex_depth i j)) h

end Blotto.RationalThreeGeometryCode
