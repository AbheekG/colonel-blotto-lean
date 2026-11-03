import Blotto.RationalAffineHeight
import Blotto.RationalExpressionBitCost

/-! Dense reflection retains all twelve products and row additions. Every
pre-final rational operand has the input height; final reflected words use
one subtraction level. Input production, indices/backend/ownership are separate. -/

namespace Blotto.RationalReflectionCode
open scoped BigOperators

abbrev Expr := RationalExpression 4

def row (j : Fin 4) : Expr :=
  .add (.add (.add (.add (.literal 0)
    (.mul (.literal (if j = 0 then -1 else 0)) (.input 0)))
      (.mul (.literal (if j = 1 then -1 else 0)) (.input 1)))
        (.mul (.literal (if j = 2 then -1 else 0)) (.input 2)))
          (if j = 3 then .literal 0 else .input 3)

def environment (length x : Fin 3 → ℚ) (j : Fin 4) : FixedArrayTable 4 ℚ :=
  FixedArrayTable.ofFn ![x 0, x 1, x 2, ![length 0, length 1, length 2, 0] j]

theorem row_value (length x : Fin 3 → ℚ) (j : Fin 4) :
    (row j).value (environment length x j) = (RationalAffineAllocation.reflectAppend length).value x j := by
  rw [RationalAffineAllocation.reflectAppend_value]
  fin_cases j <;> simp [row, environment, FixedArrayTable.read_ofFn] <;> ring

theorem row_operations (j : Fin 4) : (row j).operationBound ≤ 15 := by fin_cases j <;> decide

theorem row_intermediates (length x : Fin 3 → ℚ) (j : Fin 4) (s : ℕ) (hs : 2 ≤ s)
    (hL : ∀ k, RationalHeight (length k) s) (hX : ∀ k, RationalHeight (x k) s) :
    (row j).AllRunHeights (environment length x j) s := by
  have hZero : RationalHeight (0 : ℚ) s := (show RationalHeight (0 : ℚ) 2 by norm_num [RationalHeight]).mono hs
  have hMinusOne : RationalHeight (-1 : ℚ) s := (show RationalHeight (-1 : ℚ) 2 by norm_num [RationalHeight]).mono hs
  have hNeg : ∀ k, RationalHeight (-(x k)) s := fun k => (hX k).neg
  fin_cases j <;> simp [row, environment, FixedArrayTable.read_ofFn, RationalExpression.AllRunHeights,
    RationalExpression.run, hZero, hMinusOne, hL, hX, hNeg]

def rowBitCost (model : RationalCostModel) (length x : Fin 3 → ℚ) (j : Fin 4) : ℕ :=
  (row j).bitCost model (environment length x j) +
    rationalWordWidth ((RationalAffineAllocation.reflectAppend length).value x j)

theorem rowBitCost_bound (model : RationalCostModel) (length x : Fin 3 → ℚ) (j : Fin 4)
    (s : ℕ) (hs : 2 ≤ s) (hL : ∀ k, RationalHeight (length k) s) (hX : ∀ k, RationalHeight (x k) s) :
    rowBitCost model length x j ≤ 16 * model.rat (1 + 2 * expressionHeightBudget s 1) := by
  have hc := ((row j).bitCost_bound model _ _ (row_intermediates length x j s hs hL hX)).trans
    (Nat.mul_le_mul_right _ (row_operations j))
  have hExpr := hc.trans (Nat.mul_le_mul_left 15 (model.monotone
    (Nat.add_le_add_left (Nat.mul_le_mul_left 2 (expressionHeightBudget_ge_input s 1)) 1)))
  have hw := (rationalWordWidth_of_height (RationalAffineAllocation.reflectAppend_height length x s hs hL hX j)).trans
    (model.word_le _)
  unfold rowBitCost
  omega

def outputBitCost (model : RationalCostModel) (length x : Fin 3 → ℚ) : ℕ :=
  ∑ j : Fin 4, rowBitCost model length x j

theorem outputBitCost_bound (model : RationalCostModel) (length x : Fin 3 → ℚ)
    (s : ℕ) (hs : 2 ≤ s) (hL : ∀ k, RationalHeight (length k) s) (hX : ∀ k, RationalHeight (x k) s) :
    outputBitCost model length x ≤ 64 * model.rat (1 + 2 * expressionHeightBudget s 1) := by
  calc
    _ ≤ ∑ _j : Fin 4, 16 * model.rat (1 + 2 * expressionHeightBudget s 1) := Finset.sum_le_sum (fun j _ =>
      rowBitCost_bound model length x j s hs hL hX)
    _ = _ := by simp; ring

end Blotto.RationalReflectionCode
