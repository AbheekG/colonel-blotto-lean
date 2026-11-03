import Blotto.RationalExpressionBitCost
import Blotto.RationalThreeCodeBounds
import Blotto.RationalNestedParametersBounds
import Blotto.RationalFourParametersCode
import Blotto.RationalOverlapFormulaHeight

/-! The paper's Rat(W) profile prices actual counted local coupling programs.
Complete operand certificates and selected evaluation paths supply the bounds.
These are rational primitive/copy prices, not physical-library timing claims. -/

namespace Blotto
open scoped BigOperators

namespace RationalThreeGeometryCode

theorem chosen_bitCost (model : RationalCostModel) (g : RationalThreeGeometry) (slot : Fin 9)
    (s : ℕ) (hs : 2 ≤ s) (hEnv : ∀ j, RationalHeight ((environment g).read j) s) :
    (chosen slot).bitCost model (environment g) ≤ 256 * model.rat (1 + 2 * expressionHeightBudget s 16) := by
  have hp := (chosen slot).run_all_heights _ s hEnv ((chosen slot).LiteralHeights_mono hs (chosen_literals slot))
  have hAll := RationalExpression.AllRunHeights_mono _ _ (expressionHeightBudget_mono s (chosen_depth slot)) hp
  exact ((chosen slot).bitCost_bound model _ _ hAll).trans
    (Nat.mul_le_mul_right _ (chosen_operationBound slot))

theorem vertex_bitCost (model : RationalCostModel) (g : RationalThreeGeometry) (vertexIndex : Fin 6)
    (coordinate : Fin 3) (s : ℕ) (hs : 2 ≤ s) (hEnv : ∀ j, RationalHeight ((environment g).read j) s) :
    (vertex vertexIndex coordinate).bitCost model (environment g) ≤
      8 * model.rat (1 + 2 * expressionHeightBudget s 16) := by
  have hp := (vertex vertexIndex coordinate).run_all_heights _ s hEnv
    ((vertex vertexIndex coordinate).LiteralHeights_mono hs (vertex_literals vertexIndex coordinate))
  have hd : (vertex vertexIndex coordinate).depth ≤ 16 := (vertex_depth _ _).trans (by decide)
  have hAll := RationalExpression.AllRunHeights_mono _ _ (expressionHeightBudget_mono s hd) hp
  exact ((vertex vertexIndex coordinate).bitCost_bound model _ _ hAll).trans
    (Nat.mul_le_mul_right _ (vertex_operationBound _ _))

end RationalThreeGeometryCode
namespace RationalNestedParametersCode

theorem scalar_bitCost (model : RationalCostModel) (i : RationalNestedInput) (x : ℚ) (j : Fin 6)
    (s : ℕ) (hs : 2 ≤ s) (hEnv : ∀ k, RationalHeight ((environment i x).read k) s) :
    (scalarPrograms j).bitCost model (environment i x) ≤ 128 * model.rat (1 + 2 * expressionHeightBudget s 8) :=
  ((scalarPrograms j).bitCost_bound model _ _ (scalar_intermediates i x j s hs hEnv)).trans
    (Nat.mul_le_mul_right _ (scalar_operationBound j))

end RationalNestedParametersCode
namespace RationalFourParametersCode

theorem parameter_bitCost (model : RationalCostModel) (i : RationalFourInput) (j : Fin 8)
    (s : ℕ) (hs : 2 ≤ s) (hEnv : ∀ k, RationalHeight ((environment i).read k) s) :
    (programs j).bitCost model (environment i) ≤ 256 * model.rat (1 + 2 * expressionHeightBudget s 12) :=
  ((programs j).bitCost_bound model _ _ (intermediates i j s hs hEnv)).trans
    (Nat.mul_le_mul_right _ (operationBound j))

end RationalFourParametersCode
namespace RationalOverlapFormula
open OverlapFormulaCode

theorem weight_bitCost {k h : ℕ} (model : RationalCostModel) (G : RationalOverlapGluing k h)
    (B : ℚ) (i : Fin k) (j : Fin h) (s : ℕ) (hs : 2 ≤ s) (hFirst : G.first.HeightAt s)
    (hSecond : G.second.HeightAt s) (hD : RationalHeight G.d s) (hB : RationalHeight B s) :
    weight.bitCost model (environment G B i j) ≤ 128 * model.rat (1 + 2 * expressionHeightBudget s 9) := by
  have hp := weight_intermediates G B i j s hs hFirst hSecond hD hB
  have hAll := RationalExpression.AllRunHeights_mono _ _ (expressionHeightBudget_mono s (by decide : 7 ≤ 9)) hp
  exact (weight.bitCost_bound model _ _ hAll).trans (Nat.mul_le_mul_right _ weight_operationBound)

theorem safeP_bitCost {k h : ℕ} (model : RationalCostModel) (G : RationalOverlapGluing k h)
    (B : ℚ) (i : Fin k) (j : Fin h) (s : ℕ) (hs : 2 ≤ s) (hFirst : G.first.HeightAt s)
    (hSecond : G.second.HeightAt s) (hD : RationalHeight G.d s) (hB : RationalHeight B s) (r : Fin 4) :
    (safeP r).bitCost model (environment G B i j) ≤ 256 * model.rat (1 + 2 * expressionHeightBudget s 9) :=
  ((safeP r).bitCost_bound model _ _ (safeP_intermediates G B i j s hs hFirst hSecond hD hB r)).trans
    (Nat.mul_le_mul_right _ (safeP_operationBound r))

theorem safeQ_bitCost {k h : ℕ} (model : RationalCostModel) (G : RationalOverlapGluing k h)
    (B : ℚ) (i : Fin k) (j : Fin h) (s : ℕ) (hs : 2 ≤ s) (hFirst : G.first.HeightAt s)
    (hSecond : G.second.HeightAt s) (hD : RationalHeight G.d s) (hB : RationalHeight B s) (r : Fin 4) :
    (safeQ r).bitCost model (environment G B i j) ≤ 256 * model.rat (1 + 2 * expressionHeightBudget s 9) :=
  ((safeQ r).bitCost_bound model _ _ (safeQ_intermediates G B i j s hs hFirst hSecond hD hB r)).trans
    (Nat.mul_le_mul_right _ (safeQ_operationBound r))

end RationalOverlapFormula
end Blotto
