import Blotto.RationalThreeCompilerMetadata
import Blotto.RationalThreeInputPreparation
import Blotto.RationalPreparationCommonPrice

/-! Ordered three-input construction retains its regime/parameter environments
and the actual geometry or exceptional table branch. Child formula production,
caller frequency and physical address/backend/ownership remain separate. -/

namespace Blotto.RationalThreeInputCode
open scoped BigOperators

def constructionMetadataWork (primitive : ℕ → ℕ) (c : ℕ) (i : RationalThreeInput) : ℕ :=
  5 * rationalEnvironmentMetadataWork primitive (environment i) + RationalExpression.metadataAllowance c regime (environment i) +
    if hE : 0 < i.a + i.d - i.B then
      (∑ j : Fin 4, RationalExpression.metadataAllowance c (parameters j) (environment i)) +
        RationalThreeGeometryCode.compilerMetadataWork primitive c (i.geometry hE)
    else PreparedSegmentDescriptor.preparationMetadataBitWork primitive i.segmentLottery

def constructionMetadataBound (c s : ℕ) : ℕ :=
  5 * rationalEnvironmentMetadataBound c 5 (1 + 2 * s) + 5 * RationalExpression.metadataInstructionBound c 5 5 +
    32 * RationalExpression.metadataInstructionBound c 5 8 + rationalEnvironmentMetadataBound c 4 (1 + 2 * expressionHeightBudget s 2) +
      2736 * RationalExpression.metadataInstructionBound c 4 256 +
        PreparedSegmentDescriptor.preparationMetadataBound c 3 9 (expressionHeightBudget s 18)

theorem constructionMetadataBound_mono (c : ℕ) : Monotone (constructionMetadataBound c) := by
  intro a b hab
  have hEnv := rationalEnvironmentMetadataBound_mono c (le_refl 5) (show 1 + 2 * a ≤ 1 + 2 * b by omega)
  have h2 := expressionHeightBudget_input_mono hab 2
  have hGeometry := rationalEnvironmentMetadataBound_mono c (le_refl 4)
    (show 1 + 2 * expressionHeightBudget a 2 ≤ 1 + 2 * expressionHeightBudget b 2 by omega)
  have hTable := PreparedSegmentDescriptor.preparationMetadataBound_mono c (le_refl 3) (le_refl 9) (expressionHeightBudget_input_mono hab 18)
  unfold constructionMetadataBound
  gcongr

theorem constructionMetadataWork_bound (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w)
    (i : RationalThreeInput) (s : ℕ) (hs : 2 ≤ s) (hEnv : ∀ j, RationalHeight ((environment i).read j) s) :
    constructionMetadataWork primitive c i ≤ constructionMetadataBound c s := by
  have hEnvironment := rationalEnvironmentMetadataWork_bound primitive c hPrimitive (environment i) _
    (fun j => rationalWordWidth_of_height (hEnv j))
  have hRegime := RationalExpression.metadataAllowance_uniform_bound c regime (environment i) 5 5 le_rfl (by decide)
  unfold constructionMetadataWork
  split
  · rename_i hE
    have hParameters : (∑ j : Fin 4, RationalExpression.metadataAllowance c (parameters j) (environment i)) ≤
        32 * RationalExpression.metadataInstructionBound c 5 8 := by
      calc
        _ ≤ ∑ _j : Fin 4, 8 * RationalExpression.metadataInstructionBound c 5 8 := Finset.sum_le_sum (fun j _ =>
          RationalExpression.metadataAllowance_uniform_bound c _ _ 5 8 le_rfl (parameter_operations j))
        _ = _ := by simp; ring
    have hGeometry := RationalThreeGeometryCode.compilerMetadataWork_bound primitive c hPrimitive (i.geometry hE) _
      (hs.trans (expressionHeightBudget_ge_input s 2)) (geometry_environment_height i hE s hs hEnv)
    rw [expressionHeightBudget_comp] at hGeometry
    change RationalThreeGeometryCode.compilerMetadataWork primitive c (i.geometry hE) ≤
      rationalEnvironmentMetadataBound c 4 (1 + 2 * expressionHeightBudget s 2) +
        2736 * RationalExpression.metadataInstructionBound c 4 256 +
          PreparedSegmentDescriptor.preparationMetadataBound c 3 9 (expressionHeightBudget s 18) at hGeometry
    unfold constructionMetadataBound
    omega
  · have hTable := PreparedSegmentDescriptor.preparationMetadataBitWork_bound primitive c hPrimitive _ _ (descriptor_height i s hs hEnv)
    unfold constructionMetadataBound
    omega

end Blotto.RationalThreeInputCode
