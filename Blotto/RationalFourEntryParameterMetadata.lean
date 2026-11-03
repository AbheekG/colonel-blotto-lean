import Blotto.RationalFourParameterMetadata
import Blotto.RationalFourEntryPreparation

/-! Machine and start preparation retain four parameter-table constructions
in either regime and two regime tests. Environments are charged separately for
both tests. Descriptor/child production metadata and physical contracts remain
separate; parameter tables are not silently shared across factories. -/

namespace Blotto.RationalFourInput

def entryParameterMetadataWork (primitive : ℕ → ℕ) (c : ℕ) (i : RationalFourInput) : ℕ :=
  4 * RationalFourParameterTable.preparationMetadataWork primitive c i +
    2 * rationalEnvironmentMetadataWork primitive (RationalFourParametersCode.environment i) +
      2 * RationalExpression.metadataAllowance c RationalFourEntryCode.regime (RationalFourParametersCode.environment i)

def entryParameterMetadataBound (c s : ℕ) : ℕ :=
  4 * RationalFourParameterTable.preparationMetadataBound c s + 2 * rationalEnvironmentMetadataBound c 6 (1 + 2 * s) +
    10 * RationalExpression.metadataInstructionBound c 6 5

theorem FieldsHeight.entryParameterMetadataWork_bound {i : RationalFourInput} {s : ℕ} (h : i.FieldsHeight s) (hs : 2 ≤ s)
    (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w) :
    entryParameterMetadataWork primitive c i ≤ entryParameterMetadataBound c s := by
  have hParameters := RationalFourParameterTable.preparationMetadataWork_bound primitive c hPrimitive h hs
  have hEnvironment := rationalEnvironmentMetadataWork_bound primitive c hPrimitive (RationalFourParametersCode.environment i)
    (1 + 2 * s) (fun j => rationalWordWidth_of_height (h.environment j))
  have hRegime := RationalExpression.metadataAllowance_uniform_bound c RationalFourEntryCode.regime
    (RationalFourParametersCode.environment i) 6 5 le_rfl (by decide)
  unfold entryParameterMetadataWork entryParameterMetadataBound
  omega

noncomputable def entryPreparationWithParameterMetadataWork (model : RationalCostModel) (primitive : ℕ → ℕ) (c : ℕ)
    (i : RationalFourInput) : ℕ := i.entryPreparationAllowance model + entryParameterMetadataWork primitive c i

theorem FieldsHeight.entryPreparationWithParameterMetadataWork_bound {i : RationalFourInput} {s : ℕ}
    (h : i.FieldsHeight s) (hs : 2 ≤ s) (model : RationalCostModel) (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c * w) :
    entryPreparationWithParameterMetadataWork model primitive c i ≤
      375000 * model.rat (1 + 2 * expressionHeightBudget s 39) + entryParameterMetadataBound c s :=
  Nat.add_le_add (h.entryPreparationAllowance_bound hs model) (h.entryParameterMetadataWork_bound hs primitive c hPrimitive)

end Blotto.RationalFourInput
