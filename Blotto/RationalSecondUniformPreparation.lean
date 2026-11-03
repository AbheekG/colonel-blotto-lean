import Blotto.RationalThreeInputPreparation
import Blotto.RationalNestedResidualPreparation
import Blotto.RationalLotteryTranslateBitCost

/-! The translated uniform branch derives its actual five three-input fields,
builds that descriptor and translates both endpoint arrays. One construction is
priced; repeated caller/factory evaluation and metadata/backend remain separate. -/

namespace Blotto.RationalSecondUniformCode
open RationalNestedParametersCode
open scoped BigOperators

def programs : Fin 5 → RationalNestedParametersCode.Expr := ![.sub M mirror, A, D, .sub T mirror, .literal 1]

theorem field_value (i : RationalNestedInput) (htu : i.u ≤ i.t) (hTt : i.mirrorLength < i.t) (j : Fin 5) :
    (programs j).value (RationalNestedParametersCode.environment i 0) =
      (RationalThreeInputCode.environment (i.secondUniformInput htu hTt)).read j := by
  fin_cases j <;> simp [programs, RationalThreeInputCode.environment, FixedArrayTable.read_ofFn,
    RationalNestedInput.secondUniformInput]

theorem operations (j : Fin 5) : (programs j).operationBound ≤ 128 := by fin_cases j <;> decide

theorem depth (j : Fin 5) : (programs j).depth ≤ 9 := by fin_cases j <;> decide

theorem literals (j : Fin 5) : (programs j).LiteralHeights 2 := by
  fin_cases j <;> norm_num [programs, mirror, U, V, M, A, D, T, RationalExpression.LiteralHeights, RationalHeight]

def fieldBitCost (model : RationalCostModel) (i : RationalNestedInput) : ℕ :=
  ∑ j : Fin 5, ((programs j).bitCost model (RationalNestedParametersCode.environment i 0) +
    rationalWordWidth ((programs j).value (RationalNestedParametersCode.environment i 0)))

theorem fieldBitCost_bound (model : RationalCostModel) (i : RationalNestedInput) (s : ℕ) (hs : 2 ≤ s)
    (hEnv : ∀ j, RationalHeight ((RationalNestedParametersCode.environment i 0).read j) s) :
    fieldBitCost model i ≤ 645 * model.rat (1 + 2 * expressionHeightBudget s 9) := by
  have hp : ∀ j : Fin 5, (programs j).bitCost model (RationalNestedParametersCode.environment i 0) +
      rationalWordWidth ((programs j).value (RationalNestedParametersCode.environment i 0)) ≤
        129 * model.rat (1 + 2 * expressionHeightBudget s 9) := by
    intro j
    have hLit := (programs j).LiteralHeights_mono hs (literals j)
    have hm := expressionHeightBudget_mono s (depth j)
    have hAll := (programs j).run_all_heights _ s hEnv hLit
    have hc := ((programs j).bitCost_bound model _ _ (RationalExpression.AllRunHeights_mono _ _ hm hAll)).trans
      (Nat.mul_le_mul_right _ (operations j))
    have hv := ((programs j).run_height _ s hEnv hLit).mono hm
    change RationalHeight ((programs j).value (RationalNestedParametersCode.environment i 0)) (expressionHeightBudget s 9) at hv
    have hw := (rationalWordWidth_of_height hv).trans (model.word_le _)
    omega
  calc
    _ ≤ ∑ _j : Fin 5, 129 * model.rat (1 + 2 * expressionHeightBudget s 9) := Finset.sum_le_sum (fun j _ => hp j)
    _ = _ := by simp; ring

end Blotto.RationalSecondUniformCode
namespace Blotto.RationalNestedInput

def scalarFieldBitCost (model : RationalCostModel) (i : RationalNestedInput) (x : ℚ) (j : Fin 6) : ℕ :=
  (RationalNestedParametersCode.scalarPrograms j).bitCost model (RationalNestedParametersCode.environment i x) +
    rationalWordWidth (RationalNestedParametersCode.scalarValues i x j)

theorem FieldsHeight.scalarFieldBitCost_bound {i : RationalNestedInput} {s : ℕ} (h : i.FieldsHeight s)
    (hs : 2 ≤ s) (model : RationalCostModel) (x : ℚ) (hX : RationalHeight x s) (j : Fin 6) :
    i.scalarFieldBitCost model x j ≤ 129 * model.rat (1 + 2 * expressionHeightBudget s 8) := by
  have hc := RationalNestedParametersCode.scalar_bitCost model i x j s hs (h.environment x hX)
  have hw := (rationalWordWidth_of_height (h.scalar hs x hX j)).trans (model.word_le _)
  unfold scalarFieldBitCost
  omega

theorem FieldsHeight.secondUniformEnvironment {i : RationalNestedInput} {s : ℕ} (h : i.FieldsHeight s)
    (hs : 2 ≤ s) (htu : i.u ≤ i.t) (hTt : i.mirrorLength < i.t) :
    ∀ j, RationalHeight ((RationalThreeInputCode.environment (i.secondUniformInput htu hTt)).read j)
      (expressionHeightBudget s 9) := by
  have hZero : RationalHeight (0 : ℚ) s := (show RationalHeight (0 : ℚ) 2 by norm_num [RationalHeight]).mono hs
  have hEnv := h.environment 0 hZero
  intro j
  rw [← RationalSecondUniformCode.field_value i htu hTt j]
  have hv := (RationalSecondUniformCode.programs j).run_height _ s hEnv
    ((RationalSecondUniformCode.programs j).LiteralHeights_mono hs (RationalSecondUniformCode.literals j))
  exact hv.mono (expressionHeightBudget_mono s (RationalSecondUniformCode.depth j))

noncomputable def secondUniformPreparedBitCost (model : RationalCostModel) (i : RationalNestedInput)
    (htu : i.u ≤ i.t) (hTt : i.mirrorLength < i.t) : ℕ :=
  i.scalarFieldBitCost model 0 3 + RationalSecondUniformCode.fieldBitCost model i +
    RationalThreeInputCode.preparedInputBitCost model (i.secondUniformInput htu hTt) +
      RationalSegmentLottery.shiftThirdPreparedBitCost model (i.secondUniformInput htu hTt).segmentLottery i.mirrorLength

theorem FieldsHeight.secondUniformPreparedBitCost_bound {i : RationalNestedInput} {s : ℕ} (h : i.FieldsHeight s)
    (hs : 2 ≤ s) (model : RationalCostModel) (htu : i.u ≤ i.t) (hTt : i.mirrorLength < i.t) :
    i.secondUniformPreparedBitCost model htu hTt ≤ 3734 * model.rat (1 + 2 * expressionHeightBudget s 28) := by
  let W := 1 + 2 * expressionHeightBudget s 28
  have hZero : RationalHeight (0 : ℚ) s := (show RationalHeight (0 : ℚ) 2 by norm_num [RationalHeight]).mono hs
  have hMirror := (h.scalarFieldBitCost_bound hs model 0 hZero 3).trans (Nat.mul_le_mul_left 129
    (model.monotone (Nat.add_le_add_left (Nat.mul_le_mul_left 2 (expressionHeightBudget_mono s (by decide : 8 ≤ 28))) 1)))
  have hFields := (RationalSecondUniformCode.fieldBitCost_bound model i s hs (h.environment 0 hZero)).trans
    (Nat.mul_le_mul_left 645 (model.monotone (Nat.add_le_add_left (Nat.mul_le_mul_left 2
      (expressionHeightBudget_mono s (by decide : 9 ≤ 28))) 1)))
  have hs9 := hs.trans (expressionHeightBudget_ge_input s 9)
  have hEnv := h.secondUniformEnvironment hs htu hTt
  have hd := RationalThreeInputCode.preparedInputBitCost_bound model (i.secondUniformInput htu hTt) _ hs9 hEnv
  rw [expressionHeightBudget_comp] at hd
  have hDesc := hd.trans (Nat.mul_le_mul_left 2843 (model.monotone (Nat.add_le_add_left (Nat.mul_le_mul_left 2
    (expressionHeightBudget_mono s (by decide : 27 ≤ 28))) 1)))
  have hTable := RationalThreeInputCode.descriptor_height (i.secondUniformInput htu hTt) _ hs9 hEnv
  rw [expressionHeightBudget_comp] at hTable
  have hMirrorHeight : RationalHeight i.mirrorLength (expressionHeightBudget s 27) := by
    have hp := h.scalar hs 0 hZero 3
    change RationalHeight i.mirrorLength (expressionHeightBudget s 8) at hp
    exact hp.mono (expressionHeightBudget_mono s (by decide : 8 ≤ 27))
  have hTranslate := RationalSegmentLottery.shiftThirdPreparedBitCost_bound model _ _ _ hTable hMirrorHeight
  rw [expressionHeightBudget_comp] at hTranslate
  change i.scalarFieldBitCost model 0 3 ≤ 129 * model.rat W at hMirror
  change RationalSecondUniformCode.fieldBitCost model i ≤ 645 * model.rat W at hFields
  change RationalThreeInputCode.preparedInputBitCost model (i.secondUniformInput htu hTt) ≤ 2843 * model.rat W at hDesc
  change RationalSegmentLottery.shiftThirdPreparedBitCost model (i.secondUniformInput htu hTt).segmentLottery i.mirrorLength ≤
    117 * model.rat W at hTranslate
  change i.secondUniformPreparedBitCost model htu hTt ≤ 3734 * model.rat W
  unfold secondUniformPreparedBitCost
  omega

end Blotto.RationalNestedInput
