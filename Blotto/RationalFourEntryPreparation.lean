import Blotto.RationalFourGluingPreparation
import Blotto.RationalFourSmallPreparation
import Blotto.RationalSmallCallbackInvariant

/-! The ordered four-entry constructor and start function both test the
regime. Gluing builds its descriptor for the machine and again for the start;
small binary control constructs both machines and both start values eagerly.
Parameter tables are not shared across factories. Metadata/backend are separate. -/

namespace Blotto.RationalFourEntryCode

def regime : RationalFourParametersCode.Expr :=
  .mul (.sub (.literal 1) RationalFourParametersCode.P) RationalFourParametersCode.L

theorem regime_value (i : RationalFourInput) : regime.value (RationalFourParametersCode.environment i) = (1 - i.p) * i.ell := by
  simp [regime, RationalFourParametersCode.P, RationalFourParametersCode.L,
    RationalFourParametersCode.environment, FixedArrayTable.read_ofFn]

def regimeBitCost (model : RationalCostModel) (i : RationalFourInput) : ℕ :=
  regime.bitCost model (RationalFourParametersCode.environment i) +
    rationalWordWidth ((1 - i.p) * i.ell) + rationalWordWidth i.w +
      model.rat (RationalExpression.pairWidth ((1 - i.p) * i.ell) i.w)

theorem regimeBitCost_bound {i : RationalFourInput} {s : ℕ} (h : i.FieldsHeight s) (hs : 2 ≤ s) (model : RationalCostModel) :
    regimeBitCost model i ≤ 8 * model.rat (1 + 2 * expressionHeightBudget s 2) := by
  have hLit : regime.LiteralHeights s := by
    have hOne : RationalHeight (1 : ℚ) s := (show RationalHeight (1 : ℚ) 2 by norm_num [RationalHeight]).mono hs
    simpa [regime, RationalFourParametersCode.P, RationalFourParametersCode.L, RationalExpression.LiteralHeights] using hOne
  have hAll := regime.run_all_heights _ s h.environment hLit
  have hd : regime.depth = 2 := by decide
  rw [hd] at hAll
  have hc := regime.bitCost_bound model _ _ hAll
  have ho : regime.operationBound = 5 := by decide
  rw [ho] at hc
  have hv := regime.run_height _ s h.environment hLit
  change RationalHeight (regime.value (RationalFourParametersCode.environment i)) (expressionHeightBudget s regime.depth) at hv
  rw [regime_value, hd] at hv
  have hW := h.2.2.2.1.mono (expressionHeightBudget_ge_input s 2)
  have hValue := (rationalWordWidth_of_height hv).trans (model.word_le _)
  have hWord := (rationalWordWidth_of_height hW).trans (model.word_le _)
  have hCmp := model.monotone (RationalExpression.pairWidth_height hv hW)
  unfold regimeBitCost
  omega

end Blotto.RationalFourEntryCode
namespace Blotto.RationalFourInput
open scoped BigOperators

def gluingStartWordBitCost (i : RationalFourInput) (hcase : (1 - i.p) * i.ell ≤ i.w) : ℕ :=
  2 * ∑ slot : Fin 81, rationalWordWidth ((i.gluingDescriptor hcase).weight slot)

def uniformStartWordBitCost (i : RationalFourInput) (hcase : i.w < (1 - i.p) * i.ell) : ℕ :=
  2 * ∑ slot : Fin 9, rationalWordWidth ((i.smallUniformLottery hcase).weight slot)

theorem FieldsHeight.gluingStartWordBitCost_bound {i : RationalFourInput} {s : ℕ}
    (h : i.FieldsHeight s) (hs : 2 ≤ s) (hcase : (1 - i.p) * i.ell ≤ i.w) (model : RationalCostModel) :
    i.gluingStartWordBitCost hcase ≤ 162 * model.rat (1 + 2 * expressionHeightBudget s 36) := by
  have hp : (∑ slot : Fin 81, rationalWordWidth ((i.gluingDescriptor hcase).weight slot)) ≤
      81 * model.rat (1 + 2 * expressionHeightBudget s 36) := by
    calc
      _ ≤ ∑ _slot : Fin 81, model.rat (1 + 2 * expressionHeightBudget s 36) := Finset.sum_le_sum (fun slot _ =>
        (rationalWordWidth_of_height ((h.gluingDescriptor hs hcase).1 slot)).trans (model.word_le _))
      _ = _ := by simp
  unfold gluingStartWordBitCost
  omega

theorem FieldsHeight.uniformStartWordBitCost_bound {i : RationalFourInput} {s : ℕ}
    (h : i.FieldsHeight s) (hs : 2 ≤ s) (hcase : i.w < (1 - i.p) * i.ell) (model : RationalCostModel) :
    i.uniformStartWordBitCost hcase ≤ 18 * model.rat (1 + 2 * expressionHeightBudget s 35) := by
  have hp : (∑ slot : Fin 9, rationalWordWidth ((i.smallUniformLottery hcase).weight slot)) ≤
      9 * model.rat (1 + 2 * expressionHeightBudget s 35) := by
    calc
      _ ≤ ∑ _slot : Fin 9, model.rat (1 + 2 * expressionHeightBudget s 35) := Finset.sum_le_sum (fun slot _ =>
        (rationalWordWidth_of_height ((h.smallUniformLottery hs hcase).1 slot)).trans (model.word_le _))
      _ = _ := by simp
  unfold uniformStartWordBitCost
  omega

noncomputable def entryPreparationAllowance (model : RationalCostModel) (i : RationalFourInput) : ℕ :=
  2 * RationalFourEntryCode.regimeBitCost model i + if hcase : (1 - i.p) * i.ell ≤ i.w then
    2 * i.gluingPreparationBitCost model hcase + i.gluingStartWordBitCost hcase
  else
    2 * i.smallParentPreparationAllowance model (lt_of_not_ge hcase) +
      i.smallRootFieldBitCost + i.uniformStartWordBitCost (lt_of_not_ge hcase)

theorem FieldsHeight.entryPreparationAllowance_bound {i : RationalFourInput} {s : ℕ}
    (h : i.FieldsHeight s) (hs : 2 ≤ s) (model : RationalCostModel) :
    i.entryPreparationAllowance model ≤ 375000 * model.rat (1 + 2 * expressionHeightBudget s 39) := by
  let price := model.rat (1 + 2 * expressionHeightBudget s 39)
  have hGuard := (RationalFourEntryCode.regimeBitCost_bound h hs model).trans (Nat.mul_le_mul_left 8
    (model.heightPrice_mono (le_refl s) (by decide : 2 ≤ 39)))
  change RationalFourEntryCode.regimeBitCost model i ≤ 8 * price at hGuard
  unfold entryPreparationAllowance
  split
  · rename_i hcase
    have hGluing := h.gluingPreparationBitCost_bound hs hcase model
    have hStart := (h.gluingStartWordBitCost_bound hs hcase model).trans (Nat.mul_le_mul_left 162
      (model.heightPrice_mono (le_refl s) (by decide : 36 ≤ 39)))
    change i.gluingPreparationBitCost model hcase ≤ 187238 * price at hGluing
    change i.gluingStartWordBitCost hcase ≤ 162 * price at hStart
    omega
  · rename_i hcase
    have hSmall := (h.smallParentPreparationAllowance_bound hs (lt_of_not_ge hcase) model).trans (Nat.mul_le_mul_left 17414
      (model.heightPrice_mono (le_refl s) (by decide : 35 ≤ 39)))
    have hStart := (h.uniformStartWordBitCost_bound hs (lt_of_not_ge hcase) model).trans (Nat.mul_le_mul_left 18
      (model.heightPrice_mono (le_refl s) (by decide : 35 ≤ 39)))
    have hRoot := ProbabilityWords.ofRatBitCost_eq i.p ⟨i.p_pos.le, i.p_lt.le⟩
    have hWord := (rationalWordWidth_of_height h.2.2.2.2.2).trans ((model.word_le (1 + 2 * s)).trans
      (model.monotone (Nat.add_le_add_left (Nat.mul_le_mul_left 2 (expressionHeightBudget_ge_input s 39)) 1)))
    change i.smallParentPreparationAllowance model (lt_of_not_ge hcase) ≤ 17414 * price at hSmall
    change i.uniformStartWordBitCost (lt_of_not_ge hcase) ≤ 18 * price at hStart
    change rationalWordWidth i.p ≤ price at hWord
    change i.smallRootFieldBitCost = 2 * rationalWordWidth i.p - 1 at hRoot
    omega

end Blotto.RationalFourInput
