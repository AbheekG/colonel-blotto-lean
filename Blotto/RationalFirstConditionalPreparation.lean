import Blotto.RationalLotteryTranslateBitCost
import Blotto.RationalPreparedDescriptorCost
import Blotto.RationalNestedFieldHeight

/-! One first-conditional table materialization prices the conditional guard,
transformed geometry fields, geometric descriptor formulas, translation and
written payload. It covers the zero-probability corner. Caller factory counts,
input/environment construction, address/backend/ownership remain separate. -/

namespace Blotto.RationalNestedParametersCode
open scoped BigOperators

def firstGeometryFieldBitCost (model : RationalCostModel) (i : RationalNestedInput) (x : ℚ) : ℕ :=
  ∑ j : Fin 4, ((firstParameters j).bitCost model (environment i x) +
    rationalWordWidth ((firstParameters j).value (environment i x)))

theorem firstGeometryFieldBitCost_bound (model : RationalCostModel) (i : RationalNestedInput) (x : ℚ)
    (s : ℕ) (hs : 2 ≤ s) (hEnv : ∀ j, RationalHeight ((environment i x).read j) s) :
    firstGeometryFieldBitCost model i x ≤ 68 * model.rat (1 + 2 * expressionHeightBudget s 3) := by
  have hField : ∀ j : Fin 4,
      (firstParameters j).bitCost model (environment i x) + rationalWordWidth ((firstParameters j).value (environment i x)) ≤
        17 * model.rat (1 + 2 * expressionHeightBudget s 3) := by
    intro j
    have hLit := (firstParameters j).LiteralHeights_mono hs (first_parameter_literals j)
    have hAll := (firstParameters j).run_all_heights _ s hEnv hLit
    have hm := expressionHeightBudget_mono s (first_parameter_depth j)
    have hc := ((firstParameters j).bitCost_bound model _ _ (RationalExpression.AllRunHeights_mono _ _ hm hAll)).trans
      (Nat.mul_le_mul_right _ (first_parameter_operationBound j))
    have hv := ((firstParameters j).run_height _ s hEnv hLit).mono hm
    change RationalHeight ((firstParameters j).value (environment i x)) (expressionHeightBudget s 3) at hv
    have hw := (rationalWordWidth_of_height hv).trans (model.word_le _)
    omega
  calc
    _ ≤ ∑ _j : Fin 4, 17 * model.rat (1 + 2 * expressionHeightBudget s 3) := Finset.sum_le_sum (fun j _ => hField j)
    _ = _ := by simp; ring

def conditionalGuardBitCost (model : RationalCostModel) (i : RationalNestedInput) (x : ℚ) : ℕ :=
  (scalarPrograms 1).bitCost model (environment i x) + rationalWordWidth (0 : ℚ) +
    rationalWordWidth (i.conditionalProbability x) + model.rat (RationalExpression.pairWidth 0 (i.conditionalProbability x))

theorem conditionalGuardBitCost_bound (model : RationalCostModel) (i : RationalNestedInput) (x : ℚ)
    (s : ℕ) (hs : 2 ≤ s) (hEnv : ∀ j, RationalHeight ((environment i x).read j) s) :
    conditionalGuardBitCost model i x ≤ 131 * model.rat (1 + 2 * expressionHeightBudget s 8) := by
  let W := 1 + 2 * expressionHeightBudget s 8
  have hc := scalar_bitCost model i x 1 s hs hEnv
  have hq : RationalHeight (i.conditionalProbability x) (expressionHeightBudget s 8) := by
    simpa [scalarValues] using scalar_height i x 1 s hs hEnv
  have hz : RationalHeight (0 : ℚ) (expressionHeightBudget s 8) :=
    (show RationalHeight (0 : ℚ) 2 by norm_num [RationalHeight]).mono (hs.trans (expressionHeightBudget_ge_input s 8))
  have hp := (rationalWordWidth_of_height hq).trans (model.word_le W)
  have hzero := (rationalWordWidth_of_height hz).trans (model.word_le W)
  have hcmp := model.monotone (RationalExpression.pairWidth_height hz hq)
  change model.rat (RationalExpression.pairWidth 0 (i.conditionalProbability x)) ≤ model.rat W at hcmp
  change (scalarPrograms 1).bitCost model (environment i x) ≤ 128 * model.rat W at hc
  change conditionalGuardBitCost model i x ≤ 131 * model.rat W
  unfold conditionalGuardBitCost
  omega

end Blotto.RationalNestedParametersCode
namespace Blotto.RationalNestedInput

noncomputable def firstConditionalPreparedBitCost (model : RationalCostModel) (i : RationalNestedInput)
    (htv : i.t ≤ i.v) (x : ℚ) (hx : 0 ≤ x ∧ x ≤ i.t) : ℕ :=
  RationalNestedParametersCode.conditionalGuardBitCost model i x +
    if hp : 0 < i.conditionalProbability x then
      RationalNestedParametersCode.firstGeometryFieldBitCost model i x +
        RationalThreeGeometryCode.descriptorBitCost model (i.firstGeometry htv x hx hp) +
          RationalSegmentLottery.shiftThirdPreparedBitCost model (i.firstGeometry htv x hx hp).segmentLottery x
    else (PreparedSegmentDescriptor.prepare (i.firstConditionalLottery htv x hx)).payloadBitCost

theorem FieldsHeight.firstConditionalPreparedBitCost_bound {i : RationalNestedInput} {s : ℕ}
    (h : i.FieldsHeight s) (hs : 2 ≤ s) (model : RationalCostModel) (htv : i.t ≤ i.v)
    (x : ℚ) (hx : 0 ≤ x ∧ x ≤ i.t) (hX : RationalHeight x s) :
    i.firstConditionalPreparedBitCost model htv x hx ≤ 3052 * model.rat (1 + 2 * expressionHeightBudget s 20) := by
  let W := 1 + 2 * expressionHeightBudget s 20
  have hEnv := h.environment x hX
  have hGuard := (RationalNestedParametersCode.conditionalGuardBitCost_bound model i x s hs hEnv).trans
    (Nat.mul_le_mul_left 131 (model.monotone (Nat.add_le_add_left (Nat.mul_le_mul_left 2
      (expressionHeightBudget_mono s (by decide : 8 ≤ 20))) 1)))
  change RationalNestedParametersCode.conditionalGuardBitCost model i x ≤ 131 * model.rat W at hGuard
  unfold firstConditionalPreparedBitCost
  split
  · rename_i hp
    have hGeometry := (RationalNestedParametersCode.firstGeometryFieldBitCost_bound model i x s hs hEnv).trans
      (Nat.mul_le_mul_left 68 (model.monotone (Nat.add_le_add_left (Nat.mul_le_mul_left 2
        (expressionHeightBudget_mono s (by decide : 3 ≤ 20))) 1)))
    let g := i.firstGeometry htv x hx hp
    have hG := RationalNestedParametersCode.first_geometry_height i htv x hx hp s hs hEnv
    have hsG := hs.trans (expressionHeightBudget_ge_input s 3)
    have hDescriptor := RationalThreeGeometryCode.descriptorBitCost_bound model g _ hsG hG
    rw [expressionHeightBudget_comp] at hDescriptor
    have hFormula := hDescriptor.trans (Nat.mul_le_mul_left 2736 (model.monotone (Nat.add_le_add_left (Nat.mul_le_mul_left 2
      (expressionHeightBudget_mono s (by decide : 19 ≤ 20))) 1)))
    have hTable := RationalThreeGeometryCode.compiledLotteryReference_height g _ hsG hG
    have he : RationalThreeGeometryCode.compiledLotteryReference g = g.segmentLottery := by
      simpa only [RationalThreeGeometryCode.compiledLottery, PreparedSegmentDescriptor.lottery_eq] using
        RationalThreeGeometryCode.compiledLottery_eq g
    rw [he, expressionHeightBudget_comp] at hTable
    have hTranslation := RationalSegmentLottery.shiftThirdPreparedBitCost_bound model g.segmentLottery x _ hTable
      (hX.mono (expressionHeightBudget_ge_input s 19))
    rw [expressionHeightBudget_comp] at hTranslation
    change RationalNestedParametersCode.firstGeometryFieldBitCost model i x ≤ 68 * model.rat W at hGeometry
    change RationalThreeGeometryCode.descriptorBitCost model g ≤ 2736 * model.rat W at hFormula
    change RationalSegmentLottery.shiftThirdPreparedBitCost model g.segmentLottery x ≤ 117 * model.rat W at hTranslation
    change RationalNestedParametersCode.conditionalGuardBitCost model i x +
      (RationalNestedParametersCode.firstGeometryFieldBitCost model i x +
        RationalThreeGeometryCode.descriptorBitCost model g + RationalSegmentLottery.shiftThirdPreparedBitCost model g.segmentLottery x) ≤ 3052 * model.rat W
    omega
  · have hPayload := (PreparedSegmentDescriptor.prepare (i.firstConditionalLottery htv x hx)).payloadBitCost_bound _
      (h.firstConditional hs htv x hx hX)
    have hWord := (model.word_le (1 + 2 * expressionHeightBudget s 19)).trans
      (model.monotone (Nat.add_le_add_left (Nat.mul_le_mul_left 2 (expressionHeightBudget_mono s (by decide : 19 ≤ 20))) 1))
    have hCopies := hPayload.trans (Nat.mul_le_mul_left 63 hWord)
    change (PreparedSegmentDescriptor.prepare (i.firstConditionalLottery htv x hx)).payloadBitCost ≤ 63 * model.rat W at hCopies
    change RationalNestedParametersCode.conditionalGuardBitCost model i x +
      (PreparedSegmentDescriptor.prepare (i.firstConditionalLottery htv x hx)).payloadBitCost ≤ 3052 * model.rat W
    omega

end Blotto.RationalNestedInput
