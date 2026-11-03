import Blotto.RationalFourParameterTableCost
import Blotto.RationalThreeSpecPreparation
import Blotto.RationalNestedSpecPreparation
import Blotto.RationalPreparationCommonPrice

/-! Gluing preparation retains the two parameter-table constructions used by
the two numerical child factories, both child descriptors and the complete
overlap compiler. No parent-table sharing is assumed. Metadata/backend and
caller invocation multiplicities remain separate. -/

namespace Blotto.RationalFourInput
open scoped BigOperators

def auxiliaryScalarBitCost (model : RationalCostModel) (i : RationalFourInput) : ℕ :=
  (RationalFourParametersCode.programs 1).bitCost model (RationalFourParametersCode.environment i) +
    rationalWordWidth i.auxLength

theorem FieldsHeight.auxiliaryScalarBitCost_bound {i : RationalFourInput} {s : ℕ}
    (h : i.FieldsHeight s) (hs : 2 ≤ s) (model : RationalCostModel) :
    i.auxiliaryScalarBitCost model ≤ 257 * model.rat (1 + 2 * expressionHeightBudget s 12) := by
  have hc := RationalFourParametersCode.parameter_bitCost model i 1 s hs h.environment
  have hh := h.scalar hs 1
  change RationalHeight i.auxLength (expressionHeightBudget s 12) at hh
  have hw := (rationalWordWidth_of_height hh).trans (model.word_le _)
  unfold auxiliaryScalarBitCost
  omega

def gluingChildCopyBitCost (i : RationalFourInput) (hcase : (1 - i.p) * i.ell ≤ i.w) : ℕ :=
  2 * ((∑ j : Fin 5, rationalWordWidth ((RationalThreeSpecCode.environment (i.gluingFirstSpec hcase)).read j)) +
    ∑ j : Fin 5, rationalWordWidth ((RationalThreeSpecCode.environment (i.gluingSecondSpec hcase)).read j))

theorem FieldsHeight.gluingChildCopyBitCost_bound {i : RationalFourInput} {s : ℕ}
    (h : i.FieldsHeight s) (hs : 2 ≤ s) (hcase : (1 - i.p) * i.ell ≤ i.w) (model : RationalCostModel) :
    i.gluingChildCopyBitCost hcase ≤ 20 * model.rat (1 + 2 * expressionHeightBudget s 12) := by
  have hFirst := RationalThreeSpecCode.inputFieldCopyBitCost_bound model (i.gluingFirstSpec hcase) _
    (h.gluingFirst_environment hs hcase)
  have hSecond := RationalThreeSpecCode.inputFieldCopyBitCost_bound model (i.gluingSecondSpec hcase) _
    (h.gluingSecond_environment hs hcase)
  unfold RationalThreeSpecCode.inputFieldCopyBitCost at hFirst hSecond
  unfold gluingChildCopyBitCost
  omega

noncomputable def gluingPreparationBitCost (model : RationalCostModel) (i : RationalFourInput)
    (hcase : (1 - i.p) * i.ell ≤ i.w) : ℕ :=
  2 * RationalFourParameterTable.preparationBitCost model i + i.gluingChildCopyBitCost hcase + i.auxiliaryScalarBitCost model +
    RationalThreeSpecCode.preparedSpecBitCost model (i.gluingFirstSpec hcase) +
    RationalThreeSpecCode.preparedSpecBitCost model (i.gluingSecondSpec hcase) +
    RationalOverlapFormula.preparedDescriptorBitCost model (i.overlapData hcase) i.B

theorem FieldsHeight.gluingPreparationBitCost_bound {i : RationalFourInput} {s : ℕ}
    (h : i.FieldsHeight s) (hs : 2 ≤ s) (hcase : (1 - i.p) * i.ell ≤ i.w) (model : RationalCostModel) :
    i.gluingPreparationBitCost model hcase ≤ 187238 * model.rat (1 + 2 * expressionHeightBudget s 39) := by
  let price := model.rat (1 + 2 * expressionHeightBudget s 39)
  have hm12 : model.rat (1 + 2 * expressionHeightBudget s 12) ≤ price := model.heightPrice_mono (le_refl s) (by decide)
  have hm30 : model.rat (1 + 2 * expressionHeightBudget s 30) ≤ price := model.heightPrice_mono (le_refl s) (by decide)
  have hParams := (RationalFourParameterTable.preparationBitCost_bound h hs model).trans (Nat.mul_le_mul_left 2068 hm12)
  have hCopy := (h.gluingChildCopyBitCost_bound hs hcase model).trans (Nat.mul_le_mul_left 20 hm12)
  have hAux := (h.auxiliaryScalarBitCost_bound hs model).trans (Nat.mul_le_mul_left 257 hm12)
  have hs12 := hs.trans (expressionHeightBudget_ge_input s 12)
  have hFirst := RationalThreeSpecCode.preparedSpecBitCost_bound model (i.gluingFirstSpec hcase) _ hs12
    (h.gluingFirst_environment hs hcase)
  have hSecond := RationalThreeSpecCode.preparedSpecBitCost_bound model (i.gluingSecondSpec hcase) _ hs12
    (h.gluingSecond_environment hs hcase)
  rw [expressionHeightBudget_comp] at hFirst hSecond
  have hFirstPrice := hFirst.trans (Nat.mul_le_mul_left 2920 hm30)
  have hSecondPrice := hSecond.trans (Nat.mul_le_mul_left 2920 hm30)
  have hFirstHeight := RationalThreeSpecCode.descriptor_height (i.gluingFirstSpec hcase) _ hs12
    (h.gluingFirst_environment hs hcase)
  have hSecondHeight := RationalThreeSpecCode.descriptor_height (i.gluingSecondSpec hcase) _ hs12
    (h.gluingSecond_environment hs hcase)
  rw [expressionHeightBudget_comp] at hFirstHeight hSecondHeight
  have hD : RationalHeight i.auxLength (expressionHeightBudget s 30) := by
    have hh := h.scalar hs 1
    change RationalHeight i.auxLength (expressionHeightBudget s 12) at hh
    exact hh.mono (expressionHeightBudget_mono s (by decide : 12 ≤ 30))
  have hOverlap := RationalOverlapFormula.preparedDescriptorBitCost_bound model (i.overlapData hcase) i.B _
    (hs.trans (expressionHeightBudget_ge_input s 30)) hFirstHeight hSecondHeight hD
    (h.1.mono (expressionHeightBudget_ge_input s 30))
  rw [expressionHeightBudget_comp] at hOverlap
  change RationalOverlapFormula.preparedDescriptorBitCost model (i.overlapData hcase) i.B ≤ 176985 * price at hOverlap
  change i.gluingPreparationBitCost model hcase ≤ 187238 * price
  unfold gluingPreparationBitCost
  omega

end Blotto.RationalFourInput
