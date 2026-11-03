import Blotto.RationalThreeInputConstructionMetadata
import Blotto.RationalFirstMidpointConstructionMetadata

/-! The translated-uniform branch derives mirror and five child fields,
constructs the ordered three-input descriptor, then translates both endpoints.
Uncached scalar environments and every final slot remain priced. -/

namespace Blotto.RationalNestedInput
open scoped BigOperators

def secondUniformMetadataWork (primitive : ℕ → ℕ) (c : ℕ) (i : RationalNestedInput)
    (htu : i.u ≤ i.t) (hTt : i.mirrorLength < i.t) : ℕ :=
  6 * rationalEnvironmentMetadataWork primitive (RationalNestedParametersCode.environment i 0) +
    RationalExpression.metadataAllowance c (RationalNestedParametersCode.scalarPrograms 3) (RationalNestedParametersCode.environment i 0) +
      (∑ j : Fin 5, RationalExpression.metadataAllowance c (RationalSecondUniformCode.programs j) (RationalNestedParametersCode.environment i 0)) +
        RationalThreeInputCode.constructionMetadataWork primitive c (i.secondUniformInput htu hTt) +
          (i.secondUniformInput htu hTt).segmentLottery.shiftThirdMetadataWork primitive c i.mirrorLength

def secondUniformMetadataBound (c s : ℕ) : ℕ :=
  6 * rationalEnvironmentMetadataBound c 7 (1 + 2 * s) + 768 * RationalExpression.metadataInstructionBound c 7 128 +
    RationalThreeInputCode.constructionMetadataBound c (expressionHeightBudget s 9) +
      18 * rationalEnvironmentMetadataBound c 2 (1 + 2 * expressionHeightBudget s 27) +
        54 * RationalExpression.metadataInstructionBound c 2 3 +
          PreparedSegmentDescriptor.preparationMetadataBound c 3 9 (expressionHeightBudget s 28)

theorem secondUniformMetadataBound_mono (c : ℕ) : Monotone (secondUniformMetadataBound c) := by
  intro a b hab
  have hEnv := rationalEnvironmentMetadataBound_mono c (le_refl 7) (show 1 + 2 * a ≤ 1 + 2 * b by omega)
  have hInput := RationalThreeInputCode.constructionMetadataBound_mono c (expressionHeightBudget_input_mono hab 9)
  have h27 := expressionHeightBudget_input_mono hab 27
  have hShift := rationalEnvironmentMetadataBound_mono c (le_refl 2) (show 1 + 2 * expressionHeightBudget a 27 ≤ 1 + 2 * expressionHeightBudget b 27 by omega)
  have hTable := PreparedSegmentDescriptor.preparationMetadataBound_mono c (le_refl 3) (le_refl 9) (expressionHeightBudget_input_mono hab 28)
  unfold secondUniformMetadataBound
  gcongr

theorem FieldsHeight.secondUniformMetadataWork_bound {i : RationalNestedInput} {s : ℕ} (h : i.FieldsHeight s) (hs : 2 ≤ s)
    (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w)
    (htu : i.u ≤ i.t) (hTt : i.mirrorLength < i.t) :
    secondUniformMetadataWork primitive c i htu hTt ≤ secondUniformMetadataBound c s := by
  have hZero : RationalHeight (0 : ℚ) s := (show RationalHeight (0 : ℚ) 2 by norm_num [RationalHeight]).mono hs
  have hEnv := rationalEnvironmentMetadataWork_bound primitive c hPrimitive _ _
    (fun j => rationalWordWidth_of_height (h.environment 0 hZero j))
  have hMirror := RationalExpression.metadataAllowance_uniform_bound c (RationalNestedParametersCode.scalarPrograms 3)
    (RationalNestedParametersCode.environment i 0) 7 128 le_rfl (RationalNestedParametersCode.scalar_operationBound 3)
  have hPrograms : (∑ j : Fin 5, RationalExpression.metadataAllowance c (RationalSecondUniformCode.programs j) (RationalNestedParametersCode.environment i 0)) ≤
      640 * RationalExpression.metadataInstructionBound c 7 128 := by
    calc
      _ ≤ ∑ _j : Fin 5, 128 * RationalExpression.metadataInstructionBound c 7 128 := Finset.sum_le_sum (fun j _ =>
        RationalExpression.metadataAllowance_uniform_bound c _ _ 7 128 le_rfl (RationalSecondUniformCode.operations j))
      _ = _ := by simp; ring
  have hs9 := hs.trans (expressionHeightBudget_ge_input s 9)
  have hChild := RationalThreeInputCode.constructionMetadataWork_bound primitive c hPrimitive _ _ hs9
    (h.secondUniformEnvironment hs htu hTt)
  have hTable := RationalThreeInputCode.descriptor_height (i.secondUniformInput htu hTt) _ hs9 (h.secondUniformEnvironment hs htu hTt)
  rw [expressionHeightBudget_comp] at hTable
  have hMirrorHeight := h.scalar hs 0 hZero 3
  change RationalHeight i.mirrorLength (expressionHeightBudget s 8) at hMirrorHeight
  have hShift := RationalSegmentLottery.shiftThirdMetadataWork_bound primitive c hPrimitive _ _ _ hTable
    (hMirrorHeight.mono (expressionHeightBudget_mono s (by decide : 8 ≤ 27)))
  rw [expressionHeightBudget_comp] at hShift
  change (i.secondUniformInput htu hTt).segmentLottery.shiftThirdMetadataWork primitive c i.mirrorLength ≤
    18 * rationalEnvironmentMetadataBound c 2 (1 + 2 * expressionHeightBudget s 27) +
      54 * RationalExpression.metadataInstructionBound c 2 3 +
        PreparedSegmentDescriptor.preparationMetadataBound c 3 9 (expressionHeightBudget s 28) at hShift
  unfold secondUniformMetadataWork secondUniformMetadataBound
  omega

end Blotto.RationalNestedInput
