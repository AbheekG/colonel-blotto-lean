import Blotto.RealExpression
import Blotto.RationalExpressionValue

/-! One portable expression description for the coordinate/reflected-coordinate
four-variable overlap table. The environment contains twelve endpoint values,
two parent weights, the common interval length and the fallback budget. -/

namespace Blotto.OverlapFormulaCode

abbrev Expr := RationalExpression 16

def firstP (j : Fin 3) : Expr := .input ⟨j.val, by omega⟩
def firstQ (j : Fin 3) : Expr := .input ⟨3 + j.val, by omega⟩
def secondP (j : Fin 3) : Expr := .input ⟨6 + j.val, by omega⟩
def secondQ (j : Fin 3) : Expr := .input ⟨9 + j.val, by omega⟩
def firstWeight : Expr := .input 12
def secondWeight : Expr := .input 13
def intervalLength : Expr := .input 14
def budget : Expr := .input 15

def absolute (e : Expr) : Expr := .maximum e (.sub (.literal 0) e)
def reflectedP : Expr := .sub intervalLength (secondP 0)
def reflectedQ : Expr := .sub intervalLength (secondQ 0)
def lower : Expr := .maximum (.minimum (firstP 2) (firstQ 2)) (.minimum reflectedP reflectedQ)
def upper : Expr := .minimum (.maximum (firstP 2) (firstQ 2)) (.maximum reflectedP reflectedQ)
def weight : Expr :=
  .div (.mul (.mul (.mul intervalLength firstWeight) secondWeight)
      (.maximum (.sub upper lower) (.literal 0)))
    (.mul (absolute (.sub (firstQ 2) (firstP 2))) (absolute (.sub reflectedQ reflectedP)))

def firstInverse (z : Expr) : Expr := .div (.sub z (firstP 2)) (.sub (firstQ 2) (firstP 2))
def secondInverse (z : Expr) : Expr := .div (.sub z reflectedP) (.sub reflectedQ reflectedP)
def interpolate (a b t : Expr) : Expr := .add (.mul (.sub (.literal 1) t) a) (.mul t b)
def curve (z : Expr) : Fin 4 → Expr :=
  ![interpolate (firstP 0) (firstQ 0) (firstInverse z),
    interpolate (firstP 1) (firstQ 1) (firstInverse z),
    interpolate (secondP 1) (secondQ 1) (secondInverse z),
    interpolate (secondP 2) (secondQ 2) (secondInverse z)]
def fallback : Fin 4 → Expr := ![budget, .literal 0, .literal 0, .literal 0]
def safeP (j : Fin 4) : Expr := .ifLe weight (.literal 0) (fallback j) (curve lower j)
def safeQ (j : Fin 4) : Expr := .ifLe weight (.literal 0) (fallback j) (curve upper j)

theorem weight_operationBound : weight.operationBound ≤ 128 := by decide
theorem safeP_operationBound (j : Fin 4) : (safeP j).operationBound ≤ 256 := by fin_cases j <;> decide
theorem safeQ_operationBound (j : Fin 4) : (safeQ j).operationBound ≤ 256 := by fin_cases j <;> decide

theorem absolute_realValue (e : Expr) (env : FixedArrayTable 16 ℝ) :
    (absolute e).realValue env = |e.realValue env| := by
  simp only [absolute, RationalExpression.realValue_maximum, RationalExpression.realValue_sub,
    RationalExpression.realValue_literal, Rat.cast_zero, zero_sub]
  exact abs_eq_max_neg.symm

theorem absolute_value (e : Expr) (env : FixedArrayTable 16 ℚ) :
    (absolute e).value env = |e.value env| := by
  simp only [absolute, RationalExpression.value_maximum, RationalExpression.value_sub,
    RationalExpression.value_literal, zero_sub]
  exact abs_eq_max_neg.symm

end Blotto.OverlapFormulaCode
