import Blotto.RationalLotteryAssemblyMetadata
import Blotto.RationalThreeCompilerMetadata
import Blotto.RationalFirstConditionalPreparation
import Blotto.RationalPreparationCommonPrice

/-! First conditional preparation adds environments/control and translated
table metadata on its actual positive/zero-probability branches. Up to five
uncached scalar environments are retained. Input production, caller frequency
and physical address/backend/ownership/space remain separate. -/

namespace Blotto.RationalNestedInput
open scoped BigOperators

def firstConditionalMetadataWork (primitive : ℕ → ℕ) (c : ℕ) (i : RationalNestedInput)
    (htv : i.t ≤ i.v) (x : ℚ) (hx : 0 ≤ x ∧ x ≤ i.t) : ℕ :=
  5 * rationalEnvironmentMetadataWork primitive (RationalNestedParametersCode.environment i x) +
    RationalExpression.metadataAllowance c (RationalNestedParametersCode.scalarPrograms 1) (RationalNestedParametersCode.environment i x) +
      if hp : 0 < i.conditionalProbability x then
        (∑ j : Fin 4, RationalExpression.metadataAllowance c (RationalNestedParametersCode.firstParameters j) (RationalNestedParametersCode.environment i x)) +
          RationalThreeGeometryCode.compilerMetadataWork primitive c (i.firstGeometry htv x hx hp) +
            (i.firstGeometry htv x hx hp).segmentLottery.shiftThirdMetadataWork primitive c x
      else PreparedSegmentDescriptor.preparationMetadataBitWork primitive (i.firstConditionalLottery htv x hx)

def firstConditionalMetadataBound (c s : ℕ) : ℕ :=
  5 * rationalEnvironmentMetadataBound c 7 (1 + 2 * s) + 128 * RationalExpression.metadataInstructionBound c 7 128 +
    64 * RationalExpression.metadataInstructionBound c 7 16 + rationalEnvironmentMetadataBound c 4 (1 + 2 * expressionHeightBudget s 3) +
      2736 * RationalExpression.metadataInstructionBound c 4 256 +
        PreparedSegmentDescriptor.preparationMetadataBound c 3 9 (expressionHeightBudget s 19) +
          18 * rationalEnvironmentMetadataBound c 2 (1 + 2 * expressionHeightBudget s 19) +
            54 * RationalExpression.metadataInstructionBound c 2 3 +
              PreparedSegmentDescriptor.preparationMetadataBound c 3 9 (expressionHeightBudget s 20)

theorem firstConditionalMetadataBound_mono (c : ℕ) : Monotone (firstConditionalMetadataBound c) := by
  intro a b hab
  have hEnv := rationalEnvironmentMetadataBound_mono c (le_refl 7) (show 1 + 2 * a ≤ 1 + 2 * b by omega)
  have h3 := expressionHeightBudget_input_mono hab 3
  have h19 := expressionHeightBudget_input_mono hab 19
  have h20 := expressionHeightBudget_input_mono hab 20
  have hGeometry := rationalEnvironmentMetadataBound_mono c (le_refl 4) (show 1 + 2 * expressionHeightBudget a 3 ≤ 1 + 2 * expressionHeightBudget b 3 by omega)
  have hTranslation := rationalEnvironmentMetadataBound_mono c (le_refl 2) (show 1 + 2 * expressionHeightBudget a 19 ≤ 1 + 2 * expressionHeightBudget b 19 by omega)
  have hTable := PreparedSegmentDescriptor.preparationMetadataBound_mono c (le_refl 3) (le_refl 9) h19
  have hOutput := PreparedSegmentDescriptor.preparationMetadataBound_mono c (le_refl 3) (le_refl 9) h20
  unfold firstConditionalMetadataBound
  gcongr

theorem FieldsHeight.firstConditionalMetadataWork_bound {i : RationalNestedInput} {s : ℕ}
    (h : i.FieldsHeight s) (hs : 2 ≤ s) (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w)
    (htv : i.t ≤ i.v) (x : ℚ) (hx : 0 ≤ x ∧ x ≤ i.t) (hX : RationalHeight x s) :
    firstConditionalMetadataWork primitive c i htv x hx ≤ firstConditionalMetadataBound c s := by
  have hEnv := rationalEnvironmentMetadataWork_bound primitive c hPrimitive (RationalNestedParametersCode.environment i x) _
    (fun j => rationalWordWidth_of_height (h.environment x hX j))
  have hGuard := RationalExpression.metadataAllowance_uniform_bound c (RationalNestedParametersCode.scalarPrograms 1)
    (RationalNestedParametersCode.environment i x) 7 128 le_rfl (RationalNestedParametersCode.scalar_operationBound 1)
  unfold firstConditionalMetadataWork
  split
  · rename_i hp
    have hFields : (∑ j : Fin 4, RationalExpression.metadataAllowance c (RationalNestedParametersCode.firstParameters j)
        (RationalNestedParametersCode.environment i x)) ≤ 64 * RationalExpression.metadataInstructionBound c 7 16 := by
      calc
        _ ≤ ∑ _j : Fin 4, 16 * RationalExpression.metadataInstructionBound c 7 16 := Finset.sum_le_sum (fun j _ =>
          RationalExpression.metadataAllowance_uniform_bound c _ _ 7 16 le_rfl (RationalNestedParametersCode.first_parameter_operationBound j))
        _ = _ := by simp; ring
    let g := i.firstGeometry htv x hx hp
    have hG := RationalNestedParametersCode.first_geometry_height i htv x hx hp s hs (h.environment x hX)
    have hsG := hs.trans (expressionHeightBudget_ge_input s 3)
    have hGeometry := RationalThreeGeometryCode.compilerMetadataWork_bound primitive c hPrimitive g _ hsG hG
    rw [expressionHeightBudget_comp] at hGeometry
    change RationalThreeGeometryCode.compilerMetadataWork primitive c (i.firstGeometry htv x hx hp) ≤
      rationalEnvironmentMetadataBound c 4 (1 + 2 * expressionHeightBudget s 3) +
        2736 * RationalExpression.metadataInstructionBound c 4 256 +
          PreparedSegmentDescriptor.preparationMetadataBound c 3 9 (expressionHeightBudget s 19) at hGeometry
    have hTable := RationalThreeGeometryCode.compiledLotteryReference_height g _ hsG hG
    have hRef : RationalThreeGeometryCode.compiledLotteryReference g = g.segmentLottery := by
      simpa only [RationalThreeGeometryCode.compiledLottery, PreparedSegmentDescriptor.lottery_eq] using RationalThreeGeometryCode.compiledLottery_eq g
    rw [hRef, expressionHeightBudget_comp] at hTable
    have hShift := RationalSegmentLottery.shiftThirdMetadataWork_bound primitive c hPrimitive g.segmentLottery x _ hTable
      (hX.mono (expressionHeightBudget_ge_input s 19))
    rw [expressionHeightBudget_comp] at hShift
    change (i.firstGeometry htv x hx hp).segmentLottery.shiftThirdMetadataWork primitive c x ≤
      18 * rationalEnvironmentMetadataBound c 2 (1 + 2 * expressionHeightBudget s 19) +
        54 * RationalExpression.metadataInstructionBound c 2 3 +
          PreparedSegmentDescriptor.preparationMetadataBound c 3 9 (expressionHeightBudget s 20) at hShift
    change _ ≤ firstConditionalMetadataBound c s
    unfold firstConditionalMetadataBound
    omega
  · have hTable := PreparedSegmentDescriptor.preparationMetadataBitWork_bound primitive c hPrimitive _ _
      (h.firstConditional hs htv x hx hX)
    unfold firstConditionalMetadataBound
    omega

noncomputable def firstConditionalWithMetadataWork (model : RationalCostModel) (primitive : ℕ → ℕ) (c : ℕ)
    (i : RationalNestedInput) (htv : i.t ≤ i.v) (x : ℚ) (hx : 0 ≤ x ∧ x ≤ i.t) : ℕ :=
  i.firstConditionalPreparedBitCost model htv x hx + firstConditionalMetadataWork primitive c i htv x hx

theorem FieldsHeight.firstConditionalWithMetadataWork_bound {i : RationalNestedInput} {s : ℕ}
    (h : i.FieldsHeight s) (hs : 2 ≤ s) (model : RationalCostModel) (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c * w) (htv : i.t ≤ i.v) (x : ℚ) (hx : 0 ≤ x ∧ x ≤ i.t) (hX : RationalHeight x s) :
    firstConditionalWithMetadataWork model primitive c i htv x hx ≤
      3052 * model.rat (1 + 2 * expressionHeightBudget s 20) + firstConditionalMetadataBound c s :=
  Nat.add_le_add (h.firstConditionalPreparedBitCost_bound hs model htv x hx hX)
    (h.firstConditionalMetadataWork_bound hs primitive c hPrimitive htv x hx hX)

end Blotto.RationalNestedInput
