import Blotto.RationalSplitDescriptorCost
import Blotto.RationalThreeSpecPreparation
import Blotto.RationalMergeFourHeight
import Blotto.RationalExpressionInputOccurrences

/-! Merge/split construction prices its summed pair, child record and dense
endpoint map. Four child-price allowances retain uncached coordinate-reader
work, as exposed by the row input occurrences. Metadata/backend are separate. -/

namespace Blotto.RationalSplitCode
open scoped BigOperators

theorem row_coordinateOccurrences (j : Fin 4) (k : Fin 3) :
    (row j).inputOccurrences ⟨k.val + 2, by omega⟩ = 1 := by
  fin_cases j <;> fin_cases k <;> decide

theorem output_coordinateOccurrences (k : Fin 3) :
    (∑ j : Fin 4, (row j).inputOccurrences ⟨k.val + 2, by omega⟩) = 4 := by
  simp [row_coordinateOccurrences]

end Blotto.RationalSplitCode
namespace Blotto.RationalMergeFourInput
open scoped BigOperators

def childDataBitCost (model : RationalCostModel) (i : RationalMergeFourInput) : ℕ :=
  rationalWordWidth i.l0 + rationalWordWidth i.l1 + model.rat (RationalExpression.pairWidth i.l0 i.l1) +
    rationalWordWidth (i.l0 + i.l1) +
      2 * ∑ j : Fin 5, rationalWordWidth ((RationalThreeSpecCode.environment i.childSpec).read j)

theorem FieldsHeight.childDataBitCost_bound {i : RationalMergeFourInput} {s : ℕ} (h : i.FieldsHeight s)
    (hs : 2 ≤ s) (model : RationalCostModel) :
    i.childDataBitCost model ≤ 14 * model.rat (1 + 2 * expressionHeightBudget s 1) := by
  have hm := expressionHeightBudget_ge_input s 1
  have hA := h.2.1.mono hm
  have hD := h.2.2.1.mono hm
  have hPair : RationalHeight (i.l0 + i.l1) (expressionHeightBudget s 1) := by
    have ha : RationalHeight i.l0 (expressionHeightBudget s 0) := by simpa only [expressionHeightBudget_zero] using h.2.1
    have hd : RationalHeight i.l1 (expressionHeightBudget s 0) := by simpa only [expressionHeightBudget_zero] using h.2.2.1
    exact ha.add_level hd
  have hAw := (rationalWordWidth_of_height hA).trans (model.word_le _)
  have hDw := (rationalWordWidth_of_height hD).trans (model.word_le _)
  have hPw := (rationalWordWidth_of_height hPair).trans (model.word_le _)
  have hCall := model.monotone (RationalExpression.pairWidth_height hA hD)
  have hCopies : (∑ j : Fin 5, rationalWordWidth ((RationalThreeSpecCode.environment i.childSpec).read j)) ≤
      5 * model.rat (1 + 2 * expressionHeightBudget s 1) := by
    calc
      _ ≤ ∑ _j : Fin 5, model.rat (1 + 2 * expressionHeightBudget s 1) := Finset.sum_le_sum (fun j _ =>
        (rationalWordWidth_of_height (h.child_environment hs j)).trans (model.word_le _))
      _ = _ := by simp
  unfold childDataBitCost
  omega

noncomputable def preparedDescriptorAllowance (model : RationalCostModel) (i : RationalMergeFourInput) : ℕ :=
  i.childDataBitCost model + 4 * RationalThreeSpecCode.preparedSpecBitCost model i.childSpec +
    RationalSplitCode.preparedDescriptorBitCost model i.l0 i.l1 i.childSpec.segmentLottery

theorem FieldsHeight.preparedDescriptorAllowance_bound {i : RationalMergeFourInput} {s : ℕ} (h : i.FieldsHeight s)
    (hs : 2 ≤ s) (model : RationalCostModel) :
    i.preparedDescriptorAllowance model ≤ 13215 * model.rat (1 + 2 * expressionHeightBudget s 22) := by
  let price := model.rat (1 + 2 * expressionHeightBudget s 22)
  have hData := (h.childDataBitCost_bound hs model).trans (Nat.mul_le_mul_left 14
    (model.heightPrice_mono (le_refl s) (by decide : 1 ≤ 22)))
  have hChild := RationalThreeSpecCode.preparedSpecBitCost_bound model i.childSpec _
    (hs.trans (expressionHeightBudget_ge_input s 1)) (h.child_environment hs)
  rw [expressionHeightBudget_comp] at hChild
  have hChildPrice := hChild.trans (Nat.mul_le_mul_left 2920 (model.heightPrice_mono (le_refl s) (by decide : 19 ≤ 22)))
  have hHeight := RationalThreeSpecCode.descriptor_height i.childSpec _
    (hs.trans (expressionHeightBudget_ge_input s 1)) (h.child_environment hs)
  rw [expressionHeightBudget_comp] at hHeight
  have hSplit := RationalSplitCode.preparedDescriptorBitCost_bound model i.l0 i.l1 i.childSpec.segmentLottery _
    (hs.trans (expressionHeightBudget_ge_input s 19)) i.l0_pos i.l1_pos
    (h.2.1.mono (expressionHeightBudget_ge_input s 19)) (h.2.2.1.mono (expressionHeightBudget_ge_input s 19)) hHeight
  rw [expressionHeightBudget_comp] at hSplit
  change i.childDataBitCost model ≤ 14 * price at hData
  change RationalThreeSpecCode.preparedSpecBitCost model i.childSpec ≤ 2920 * price at hChildPrice
  change RationalSplitCode.preparedDescriptorBitCost model i.l0 i.l1 i.childSpec.segmentLottery ≤ 1521 * price at hSplit
  change i.preparedDescriptorAllowance model ≤ 13215 * price
  unfold preparedDescriptorAllowance
  omega

end Blotto.RationalMergeFourInput
