import Blotto.RationalResidualCompilerMetadata
import Blotto.RationalLotteryAssemblyMetadata

/-! Actual residual input field derivation, complete residual table metadata
and optional six-slot padding compose before the third-profile length guard.
All slots are priced; caller frequency and physical contracts remain separate. -/

namespace Blotto.RationalNestedInput
open scoped BigOperators

def paddedResidualMetadataWork (primitive : ℕ → ℕ) (c : ℕ) (i : RationalNestedInput)
    (hvt : i.v < i.t) (htu : i.t < i.u) : ℕ :=
  5 * rationalEnvironmentMetadataWork primitive (RationalNestedParametersCode.environment i 0) +
    (∑ j : Fin 5, RationalExpression.metadataAllowance c (RationalNestedResidualPreparationCode.programs j) (RationalNestedParametersCode.environment i 0)) +
      RationalNestedResidualCode.compilerMetadataWork primitive c (i.residualInput hvt htu) +
        (i.residualInput hvt htu).segmentLottery.paddingMetadataWork primitive 6 0

def paddedResidualMetadataBound (c s : ℕ) : ℕ :=
  5 * rationalEnvironmentMetadataBound c 7 (1 + 2 * s) + 80 * RationalExpression.metadataInstructionBound c 7 16 +
    RationalNestedResidualCode.compilerMetadataBound c (expressionHeightBudget s 2) +
      PreparedSegmentDescriptor.preparationMetadataBound c 3 9 (expressionHeightBudget s 10)

theorem paddedResidualMetadataBound_mono (c : ℕ) : Monotone (paddedResidualMetadataBound c) := by
  intro a b hab
  have hEnv := rationalEnvironmentMetadataBound_mono c (le_refl 7) (show 1 + 2 * a ≤ 1 + 2 * b by omega)
  have hResidual := RationalNestedResidualCode.compilerMetadataBound_mono c (expressionHeightBudget_input_mono hab 2)
  have hTable := PreparedSegmentDescriptor.preparationMetadataBound_mono c (le_refl 3) (le_refl 9) (expressionHeightBudget_input_mono hab 10)
  unfold paddedResidualMetadataBound
  gcongr

theorem FieldsHeight.paddedResidualMetadataWork_bound {i : RationalNestedInput} {s : ℕ} (h : i.FieldsHeight s) (hs : 2 ≤ s)
    (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w) (hvt : i.v < i.t) (htu : i.t < i.u) :
    paddedResidualMetadataWork primitive c i hvt htu ≤ paddedResidualMetadataBound c s := by
  have hZero : RationalHeight (0 : ℚ) s := (show RationalHeight (0 : ℚ) 2 by norm_num [RationalHeight]).mono hs
  have hEnv := rationalEnvironmentMetadataWork_bound primitive c hPrimitive _ _
    (fun j => rationalWordWidth_of_height (h.environment 0 hZero j))
  have hPrograms : (∑ j : Fin 5, RationalExpression.metadataAllowance c (RationalNestedResidualPreparationCode.programs j)
      (RationalNestedParametersCode.environment i 0)) ≤ 80 * RationalExpression.metadataInstructionBound c 7 16 := by
    calc
      _ ≤ ∑ _j : Fin 5, 16 * RationalExpression.metadataInstructionBound c 7 16 := Finset.sum_le_sum (fun j _ =>
        RationalExpression.metadataAllowance_uniform_bound c _ _ 7 16 le_rfl (RationalNestedResidualPreparationCode.operations j))
      _ = _ := by simp; ring
  have hResidual := RationalNestedResidualCode.compilerMetadataWork_bound primitive c hPrimitive _ _
    (hs.trans (expressionHeightBudget_ge_input s 2)) (h.residualEnvironment hs hvt htu)
  have hPadding := RationalSegmentLottery.paddingMetadataWork_bound primitive c hPrimitive _ 6 0 _
    (hs.trans (expressionHeightBudget_ge_input s 10)) (h.residual hs hvt htu)
  exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left 5 hEnv) hPrograms) hResidual) hPadding

end Blotto.RationalNestedInput
