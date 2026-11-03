import Blotto.RationalNestedParametersCode
import Blotto.RationalExpressionIntermediates

/-! Constant counted bounds and complete argument-height certificates for
native nested scalar parameters and first-case geometric transformation. -/

namespace Blotto.RationalNestedParametersCode

def scalarPrograms : Fin 6 → Expr := ![location, conditional, familyProbability, mirror, secondAlpha, thirdAlpha]

def scalarValues (i : RationalNestedInput) (x : ℚ) : Fin 6 → ℚ :=
  ![i.location x, i.conditionalProbability x, i.familyProbability x, i.mirrorLength, i.secondAlpha, i.thirdAlpha]

theorem scalar_value (i : RationalNestedInput) (x : ℚ) (j : Fin 6) :
    (scalarPrograms j).value (environment i x) = scalarValues i x j := by
  fin_cases j <;> simp [scalarPrograms, scalarValues]

theorem scalar_operationBound (j : Fin 6) : (scalarPrograms j).operationBound ≤ 128 := by fin_cases j <;> decide

theorem scalar_depth (j : Fin 6) : (scalarPrograms j).depth ≤ 8 := by fin_cases j <;> decide

theorem scalar_literals (j : Fin 6) : (scalarPrograms j).LiteralHeights 2 := by
  fin_cases j <;> norm_num [scalarPrograms, location, conditional, familyProbability, mirror, secondAlpha, thirdAlpha,
    M, A, D, C, T, Q, X, U, V, H, RationalExpression.LiteralHeights, RationalHeight]

theorem first_parameter_operationBound (j : Fin 4) : (firstParameters j).operationBound ≤ 16 := by fin_cases j <;> decide

theorem first_parameter_depth (j : Fin 4) : (firstParameters j).depth ≤ 3 := by fin_cases j <;> decide

theorem first_parameter_literals (j : Fin 4) : (firstParameters j).LiteralHeights 2 := by
  fin_cases j <;> norm_num [firstParameters, M, A, D, C, T, Q, X, U, V, H, RationalExpression.LiteralHeights, RationalHeight]

theorem scalar_height (i : RationalNestedInput) (x : ℚ) (j : Fin 6) (s : ℕ) (hs : 2 ≤ s)
    (hEnv : ∀ k, RationalHeight ((environment i x).read k) s) :
    RationalHeight (scalarValues i x j) (expressionHeightBudget s 8) := by
  have h := (scalarPrograms j).run_height _ s hEnv ((scalarPrograms j).LiteralHeights_mono hs (scalar_literals j))
  have hm := h.mono (expressionHeightBudget_mono s (scalar_depth j))
  change RationalHeight ((scalarPrograms j).value (environment i x)) _ at hm
  rw [scalar_value] at hm
  exact hm

theorem scalar_wordWidth (i : RationalNestedInput) (x : ℚ) (j : Fin 6) (s : ℕ) (hs : 2 ≤ s)
    (hEnv : ∀ k, RationalHeight ((environment i x).read k) s) :
    rationalWordWidth (scalarValues i x j) ≤ 1 + 2 * expressionHeightBudget s 8 :=
  rationalWordWidth_of_height (scalar_height i x j s hs hEnv)

theorem scalar_intermediates (i : RationalNestedInput) (x : ℚ) (j : Fin 6) (s : ℕ) (hs : 2 ≤ s)
    (hEnv : ∀ k, RationalHeight ((environment i x).read k) s) :
    (scalarPrograms j).AllRunHeights (environment i x) (expressionHeightBudget s 8) := by
  have h := (scalarPrograms j).run_all_heights _ s hEnv ((scalarPrograms j).LiteralHeights_mono hs (scalar_literals j))
  exact RationalExpression.AllRunHeights_mono _ _ (expressionHeightBudget_mono s (scalar_depth j)) h

theorem scalar_operations (i : RationalNestedInput) (x : ℚ) (j : Fin 6) :
    ((scalarPrograms j).run (environment i x)).2 ≤ 128 :=
  ((scalarPrograms j).run_operations_le _).trans (scalar_operationBound j)

theorem first_geometry_height (i : RationalNestedInput) (htv : i.t ≤ i.v) (x : ℚ)
    (hx : 0 ≤ x ∧ x ≤ i.t) (hp : 0 < i.conditionalProbability x) (s : ℕ) (hs : 2 ≤ s)
    (hEnv : ∀ k, RationalHeight ((environment i x).read k) s) :
    ∀ j, RationalHeight ((RationalThreeGeometryCode.environment (i.firstGeometry htv x hx hp)).read j) (expressionHeightBudget s 3) := by
  intro j
  have h := (firstParameters j).run_height _ s hEnv ((firstParameters j).LiteralHeights_mono hs (first_parameter_literals j))
  have hm := h.mono (expressionHeightBudget_mono s (first_parameter_depth j))
  change RationalHeight ((firstParameters j).value (environment i x)) _ at hm
  rw [firstParameters_value] at hm
  exact hm

end Blotto.RationalNestedParametersCode
