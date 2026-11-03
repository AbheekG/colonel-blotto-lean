import Blotto.RationalDescriptorBitCost
import Blotto.RationalFourGluingHeight
import Blotto.RationalFourParameterTable

/-! One actual eight-entry parameter-table construction prices six input
read/write words, the eight counted formulas and eight result writes.
Indices, allocation/backend/ownership and repeated caller construction are separate. -/

namespace Blotto.RationalFourParameterTable
open scoped BigOperators

def payloadBitCost {i : RationalFourInput} (p : RationalFourParameterTable i) : ℕ :=
  ∑ j : Fin 8, rationalWordWidth (p.table.read j)

theorem payloadBitCost_bound {i : RationalFourInput} {s : ℕ} (p : RationalFourParameterTable i)
    (h : i.FieldsHeight s) (hs : 2 ≤ s) (model : RationalCostModel) :
    p.payloadBitCost ≤ 8 * model.rat (1 + 2 * expressionHeightBudget s 12) := by
  calc
    _ ≤ ∑ _j : Fin 8, model.rat (1 + 2 * expressionHeightBudget s 12) := Finset.sum_le_sum (fun j _ => by
      rw [p.correct]
      exact (rationalWordWidth_of_height (h.scalar hs j)).trans (model.word_le _))
    _ = _ := by simp

def inputCopyBitCost (i : RationalFourInput) : ℕ :=
  2 * ∑ j : Fin 6, rationalWordWidth ((RationalFourParametersCode.environment i).read j)

theorem inputCopyBitCost_bound {i : RationalFourInput} {s : ℕ} (h : i.FieldsHeight s) (model : RationalCostModel) :
    inputCopyBitCost i ≤ 12 * model.rat (1 + 2 * s) := by
  have hp : (∑ j : Fin 6, rationalWordWidth ((RationalFourParametersCode.environment i).read j)) ≤ 6 * model.rat (1 + 2 * s) := by
    calc
      _ ≤ ∑ _j : Fin 6, model.rat (1 + 2 * s) := Finset.sum_le_sum (fun j _ =>
        (rationalWordWidth_of_height (h.environment j)).trans (model.word_le _))
      _ = _ := by simp
  unfold inputCopyBitCost
  omega

def preparationBitCost (model : RationalCostModel) (i : RationalFourInput) : ℕ :=
  inputCopyBitCost i + RationalFourParametersCode.parametersBitCost model i + (prepare i).payloadBitCost

theorem preparationBitCost_bound {i : RationalFourInput} {s : ℕ} (h : i.FieldsHeight s) (hs : 2 ≤ s) (model : RationalCostModel) :
    preparationBitCost model i ≤ 2068 * model.rat (1 + 2 * expressionHeightBudget s 12) := by
  have hCopy := (inputCopyBitCost_bound h model).trans (Nat.mul_le_mul_left 12 (model.monotone
    (Nat.add_le_add_left (Nat.mul_le_mul_left 2 (expressionHeightBudget_ge_input s 12)) 1)))
  have hFormula := RationalFourParametersCode.parametersBitCost_bound model i s hs h.environment
  have hPayload := (prepare i).payloadBitCost_bound h hs model
  unfold preparationBitCost
  omega

end Blotto.RationalFourParameterTable
