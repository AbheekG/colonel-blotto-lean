import Blotto.RationalThreeWeightsCode
import Blotto.RationalExpressionLiteralHeight

/-! Explicit constant operation and linear word-height bounds for the actual
three-variable native vertices and selected segment-weight formulas. -/

namespace Blotto.RationalThreeGeometryCode

theorem chosen_literals (slot : Fin 9) : (chosen slot).LiteralHeights 2 := by
  fin_cases slot <;> norm_num [chosen, first, second, third, U, V, W, H, A, D, C, E, F, G, R, S,
    RationalExpression.LiteralHeights, RationalExpression.power, RationalHeight]

theorem vertex_literals (i : Fin 6) (j : Fin 3) : (vertex i j).LiteralHeights 2 := by
  fin_cases i <;> fin_cases j <;> norm_num [vertex, U, V, W, H, A, D, C, RationalExpression.LiteralHeights, RationalHeight]

theorem vertex_depth (i : Fin 6) (j : Fin 3) : (vertex i j).depth ≤ 2 := by
  fin_cases i <;> fin_cases j <;> decide

theorem vertex_operationBound (i : Fin 6) (j : Fin 3) : (vertex i j).operationBound ≤ 8 := by
  fin_cases i <;> fin_cases j <;> decide

theorem chosen_operations (g : RationalThreeGeometry) (slot : Fin 9) :
    ((chosen slot).run (environment g)).2 ≤ 256 :=
  ((chosen slot).run_operations_le _).trans (chosen_operationBound slot)

theorem vertex_operations (g : RationalThreeGeometry) (i : Fin 6) (j : Fin 3) :
    ((vertex i j).run (environment g)).2 ≤ 8 :=
  ((vertex i j).run_operations_le _).trans (vertex_operationBound i j)

theorem chosen_height (g : RationalThreeGeometry) (slot : Fin 9) (s : ℕ) (hs : 2 ≤ s)
    (hEnv : ∀ j, RationalHeight ((environment g).read j) s) :
    RationalHeight (g.chosenWeights slot) (expressionHeightBudget s 16) := by
  have h := (chosen slot).run_height (environment g) s hEnv ((chosen slot).LiteralHeights_mono hs (chosen_literals slot))
  have hm := h.mono (expressionHeightBudget_mono s (chosen_depth slot))
  change RationalHeight ((chosen slot).value (environment g)) (expressionHeightBudget s 16) at hm
  rw [chosen_value] at hm
  exact hm

theorem vertex_height (g : RationalThreeGeometry) (i : Fin 6) (j : Fin 3) (s : ℕ) (hs : 2 ≤ s)
    (hEnv : ∀ j, RationalHeight ((environment g).read j) s) :
    RationalHeight (g.vertex i j) (expressionHeightBudget s 2) := by
  have h := (vertex i j).run_height (environment g) s hEnv ((vertex i j).LiteralHeights_mono hs (vertex_literals i j))
  have hm := h.mono (expressionHeightBudget_mono s (vertex_depth i j))
  change RationalHeight ((vertex i j).value (environment g)) (expressionHeightBudget s 2) at hm
  rw [vertex_value] at hm
  exact hm

theorem chosen_wordWidth (g : RationalThreeGeometry) (slot : Fin 9) (s : ℕ) (hs : 2 ≤ s)
    (hEnv : ∀ j, RationalHeight ((environment g).read j) s) :
    rationalWordWidth (g.chosenWeights slot) ≤ 1 + 2 * expressionHeightBudget s 16 :=
  rationalWordWidth_of_height (chosen_height g slot s hs hEnv)

theorem vertex_wordWidth (g : RationalThreeGeometry) (i : Fin 6) (j : Fin 3) (s : ℕ) (hs : 2 ≤ s)
    (hEnv : ∀ j, RationalHeight ((environment g).read j) s) :
    rationalWordWidth (g.vertex i j) ≤ 1 + 2 * expressionHeightBudget s 2 :=
  rationalWordWidth_of_height (vertex_height g i j s hs hEnv)

end Blotto.RationalThreeGeometryCode
