import Blotto.RationalThreeInputPreparation
import Blotto.RationalPreparationComparison
import Blotto.RationalNestedSpecHeight

/-! The unsorted three-spec preparation retains separate min/max/branch
comparisons, copied ordered fields and the selected output permutation.
No common-subexpression reuse or physical ownership claim is assumed. -/

namespace Blotto.RationalThreeSpecCode
open scoped BigOperators

def orderedFieldCopyBitCost (i : RationalThreeSpec) : ℕ :=
  ∑ j : Fin 5, rationalWordWidth ((RationalThreeInputCode.environment i.orderedInput).read j)

theorem orderedFieldCopyBitCost_bound (model : RationalCostModel) (i : RationalThreeSpec) (s : ℕ)
    (hEnv : ∀ j, RationalHeight ((environment i).read j) s) :
    orderedFieldCopyBitCost i ≤ 5 * model.rat (1 + 2 * s) := by
  have hOrdered := ordered_environment_height i s hEnv
  calc
    _ ≤ ∑ _j : Fin 5, model.rat (1 + 2 * s) := Finset.sum_le_sum (fun j _ =>
      (rationalWordWidth_of_height (hOrdered j)).trans (model.word_le _))
    _ = _ := by simp

noncomputable def preparedSpecBitCost (model : RationalCostModel) (i : RationalThreeSpec) : ℕ :=
  orderedFieldCopyBitCost i + 3 * RationalPreparationComparison.bitCost model i.a i.d +
    RationalThreeInputCode.preparedInputBitCost model i.orderedInput +
      if i.a ≤ i.d then 0 else (PreparedSegmentDescriptor.prepare i.segmentLottery).payloadBitCost

theorem preparedSpecBitCost_bound (model : RationalCostModel) (i : RationalThreeSpec) (s : ℕ) (hs : 2 ≤ s)
    (hEnv : ∀ j, RationalHeight ((environment i).read j) s) :
    preparedSpecBitCost model i ≤ 2920 * model.rat (1 + 2 * expressionHeightBudget s 18) := by
  let W := 1 + 2 * expressionHeightBudget s 18
  have hm := model.monotone (Nat.add_le_add_left (Nat.mul_le_mul_left 2 (expressionHeightBudget_ge_input s 18)) 1)
  have hCopy := (orderedFieldCopyBitCost_bound model i s hEnv).trans (Nat.mul_le_mul_left 5 hm)
  have hA : RationalHeight i.a s := by simpa [environment, FixedArrayTable.read_ofFn] using hEnv 1
  have hD : RationalHeight i.d s := by simpa [environment, FixedArrayTable.read_ofFn] using hEnv 2
  have hCmp := (RationalPreparationComparison.bitCost_bound model i.a i.d s hA hD).trans (Nat.mul_le_mul_left 3 hm)
  have hInput := RationalThreeInputCode.preparedInputBitCost_bound model i.orderedInput s hs (ordered_environment_height i s hEnv)
  have hPayload := (PreparedSegmentDescriptor.prepare i.segmentLottery).payloadBitCost_bound _ (descriptor_height i s hs hEnv)
  have hWords := hPayload.trans (Nat.mul_le_mul_left 63 (model.word_le W))
  change orderedFieldCopyBitCost i ≤ 5 * model.rat W at hCopy
  change RationalPreparationComparison.bitCost model i.a i.d ≤ 3 * model.rat W at hCmp
  change RationalThreeInputCode.preparedInputBitCost model i.orderedInput ≤ 2843 * model.rat W at hInput
  change preparedSpecBitCost model i ≤ 2920 * model.rat W
  unfold preparedSpecBitCost
  split <;> omega

end Blotto.RationalThreeSpecCode
