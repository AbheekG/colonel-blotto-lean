import Blotto.RationalFourInput
import Blotto.RationalExpressionIntermediates
import Blotto.RationalExpressionLiteralHeight

/-! Counted rational programs for the native ordered four-variable scalar
parameters. The maximum and all rational divisions retain their total native
semantics; no numerical separation assumption is introduced. -/

namespace Blotto.RationalFourParametersCode

abbrev Expr := RationalExpression 6
def B : Expr := .input 0
def U : Expr := .input 1
def V : Expr := .input 2
def W : Expr := .input 3
def L : Expr := .input 4
def P : Expr := .input 5
def S : Expr := .add (.add U V) W
def auxiliary : Expr := .maximum (.maximum (.maximum (.sub V U) (.sub W (.mul P L)))
    (.sub (.mul (.sub (.literal 2) P) L) W)) (.literal 0)
def firstBudget : Expr := .div (.add (.add U V) auxiliary) (.literal 2)
def secondBudget : Expr := .div (.add (.add auxiliary W) (.mul P L)) (.literal 2)
def shortFraction : Expr := .div (.mul (.sub (.literal 1) P) L) S
def scaleFraction : Expr := .sub (.literal 1) shortFraction
def nestedProbability : Expr := .div (.mul P L) (.sub S (.mul (.sub (.literal 1) P) L))
def reflectedBudget : Expr := .div (.sub S (.mul P L)) (.literal 2)
def programs : Fin 8 → Expr := ![S, auxiliary, firstBudget, secondBudget, shortFraction, scaleFraction,
    nestedProbability, reflectedBudget]
def values (i : RationalFourInput) : Fin 8 → ℚ := ![i.S, i.auxLength, i.firstBudget, i.secondBudget,
    i.shortFraction, i.scaleFraction, i.nestedProbability, i.reflectedBudget]
def environment (i : RationalFourInput) : FixedArrayTable 6 ℚ := FixedArrayTable.ofFn ![i.B, i.u, i.v, i.w, i.ell, i.p]

theorem value_eq (i : RationalFourInput) (j : Fin 8) :
    (programs j).value (environment i) = values i j := by
  fin_cases j <;> simp [programs, values, S, auxiliary, firstBudget, secondBudget, shortFraction,
    scaleFraction, nestedProbability, reflectedBudget, U, V, W, L, P, environment,
    FixedArrayTable.read_ofFn, RationalFourInput.S, RationalFourInput.auxLength,
    RationalFourInput.firstBudget, RationalFourInput.secondBudget, RationalFourInput.shortFraction,
    RationalFourInput.scaleFraction, RationalFourInput.nestedProbability, RationalFourInput.reflectedBudget]

theorem operationBound (j : Fin 8) : (programs j).operationBound ≤ 256 := by fin_cases j <;> decide
theorem depth (j : Fin 8) : (programs j).depth ≤ 12 := by fin_cases j <;> decide
theorem literals (j : Fin 8) : (programs j).LiteralHeights 2 := by
  fin_cases j <;> norm_num [programs, S, auxiliary, firstBudget, secondBudget, shortFraction,
    scaleFraction, nestedProbability, reflectedBudget, U, V, W, L, P, RationalExpression.LiteralHeights, RationalHeight]

theorem height (i : RationalFourInput) (j : Fin 8) (s : ℕ) (hs : 2 ≤ s)
    (hEnv : ∀ r, RationalHeight ((environment i).read r) s) :
    RationalHeight (values i j) (expressionHeightBudget s 12) := by
  have h := ((programs j).run_height _ s hEnv ((programs j).LiteralHeights_mono hs (literals j))).mono
    (expressionHeightBudget_mono s (depth j))
  change RationalHeight ((programs j).value (environment i)) _ at h
  rw [value_eq] at h
  exact h

theorem wordWidth (i : RationalFourInput) (j : Fin 8) (s : ℕ) (hs : 2 ≤ s)
    (hEnv : ∀ r, RationalHeight ((environment i).read r) s) :
    rationalWordWidth (values i j) ≤ 1 + 2 * expressionHeightBudget s 12 :=
  rationalWordWidth_of_height (height i j s hs hEnv)

theorem operations (i : RationalFourInput) (j : Fin 8) :
    ((programs j).run (environment i)).2 ≤ 256 := ((programs j).run_operations_le _).trans (operationBound j)

theorem intermediates (i : RationalFourInput) (j : Fin 8) (s : ℕ) (hs : 2 ≤ s)
    (hEnv : ∀ r, RationalHeight ((environment i).read r) s) :
    (programs j).AllRunHeights (environment i) (expressionHeightBudget s 12) := by
  have h := (programs j).run_all_heights _ s hEnv ((programs j).LiteralHeights_mono hs (literals j))
  exact RationalExpression.AllRunHeights_mono _ _ (expressionHeightBudget_mono s (depth j)) h

end Blotto.RationalFourParametersCode
