import Blotto.RationalExpressionBitCost

/-! One scalar-times-row pass reads the scale and each coordinate, calls one
rational multiplication, and writes each result. Row production and physical
allocation/addressing are outside this pass. -/

namespace Blotto.RationalScaleRowCode
open scoped BigOperators

def coordinateBitCost (model : RationalCostModel) (a x : ℚ) : ℕ :=
  rationalWordWidth a + rationalWordWidth x + model.rat (RationalExpression.pairWidth a x) +
    rationalWordWidth (a * x)

def rowBitCost {n : ℕ} (model : RationalCostModel) (a : ℚ) (row : Fin n → ℚ) : ℕ :=
  ∑ j, coordinateBitCost model a (row j)

theorem coordinateBitCost_bound (model : RationalCostModel) (a x : ℚ) (s t : ℕ)
    (hA : RationalHeight a s) (hX : RationalHeight x t) :
    coordinateBitCost model a x ≤ 4 * model.rat (1 + 2 * (s + t)) := by
  have ha := (rationalWordWidth_of_height (hA.mono (Nat.le_add_right s t))).trans (model.word_le _)
  have hx := (rationalWordWidth_of_height (hX.mono (Nat.le_add_left t s))).trans (model.word_le _)
  have hm := model.monotone (RationalExpression.pairWidth_height
    (hA.mono (Nat.le_add_right s t)) (hX.mono (Nat.le_add_left t s)))
  have ho := (rationalWordWidth_of_height (hA.mul hX)).trans (model.word_le _)
  unfold coordinateBitCost
  omega

theorem rowBitCost_bound {n : ℕ} (model : RationalCostModel) (a : ℚ) (row : Fin n → ℚ) (s t : ℕ)
    (hA : RationalHeight a s) (hX : ∀ j, RationalHeight (row j) t) :
    rowBitCost model a row ≤ 4 * n * model.rat (1 + 2 * (s + t)) := by
  calc
    _ ≤ ∑ _j : Fin n, 4 * model.rat (1 + 2 * (s + t)) :=
      Finset.sum_le_sum (fun j _ => coordinateBitCost_bound model a (row j) s t hA (hX j))
    _ = _ := by simp; ring

end Blotto.RationalScaleRowCode
