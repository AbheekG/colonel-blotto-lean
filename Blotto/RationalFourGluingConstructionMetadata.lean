import Blotto.RationalFourGluingPreparation
import Blotto.RationalThreeSpecConstructionMetadata
import Blotto.RationalOverlapCompilerMetadata

/-! One gluing parent retains both child constructors, uncached copied input
environments, auxiliary evaluation and every overlap compiler environment.
The entry ledger supplies parameter-table and machine/start multiplicities. -/

namespace Blotto.RationalFourInput

def gluingConstructionMetadataWork (primitive : ℕ → ℕ) (c : ℕ) (i : RationalFourInput)
    (hcase : (1 - i.p) * i.ell ≤ i.w) : ℕ :=
  rationalEnvironmentMetadataWork primitive (RationalThreeSpecCode.environment (i.gluingFirstSpec hcase)) +
    rationalEnvironmentMetadataWork primitive (RationalThreeSpecCode.environment (i.gluingSecondSpec hcase)) +
      rationalEnvironmentMetadataWork primitive (RationalFourParametersCode.environment i) +
        RationalExpression.metadataAllowance c (RationalFourParametersCode.programs 1) (RationalFourParametersCode.environment i) +
          RationalThreeSpecCode.constructionMetadataWork primitive c (i.gluingFirstSpec hcase) +
            RationalThreeSpecCode.constructionMetadataWork primitive c (i.gluingSecondSpec hcase) +
              RationalOverlapFormula.compilerMetadataWork primitive c (i.overlapData hcase) i.B

def gluingConstructionMetadataBound (c s : ℕ) : ℕ :=
  2 * rationalEnvironmentMetadataBound c 5 (1 + 2 * expressionHeightBudget s 12) +
    rationalEnvironmentMetadataBound c 6 (1 + 2 * s) + 256 * RationalExpression.metadataInstructionBound c 6 256 +
      2 * RationalThreeSpecCode.constructionMetadataBound c (expressionHeightBudget s 12) +
        9 * (81 * rationalEnvironmentMetadataBound c 16 (1 + 2 * expressionHeightBudget s 30)) +
          2176 * 81 * RationalExpression.metadataInstructionBound c 16 256 +
            9 * (81 * RationalOverlapFormula.slotIndexMetadataUnitBound c 9 9) +
              PreparedSegmentDescriptor.preparationMetadataBound c 4 81 (expressionHeightBudget s 39)

theorem FieldsHeight.gluingConstructionMetadataWork_bound {i : RationalFourInput} {s : ℕ}
    (h : i.FieldsHeight s) (hs : 2 ≤ s) (hcase : (1 - i.p) * i.ell ≤ i.w)
    (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w) :
    gluingConstructionMetadataWork primitive c i hcase ≤ gluingConstructionMetadataBound c s := by
  have hFirstEnv := rationalEnvironmentMetadataWork_bound primitive c hPrimitive _ _
    (fun j => rationalWordWidth_of_height (h.gluingFirst_environment hs hcase j))
  have hSecondEnv := rationalEnvironmentMetadataWork_bound primitive c hPrimitive _ _
    (fun j => rationalWordWidth_of_height (h.gluingSecond_environment hs hcase j))
  have hAuxEnv := rationalEnvironmentMetadataWork_bound primitive c hPrimitive _ _
    (fun j => rationalWordWidth_of_height (h.environment j))
  have hAux := RationalExpression.metadataAllowance_uniform_bound c (RationalFourParametersCode.programs 1)
    (RationalFourParametersCode.environment i) 6 256 le_rfl (RationalFourParametersCode.operationBound 1)
  have hs12 := hs.trans (expressionHeightBudget_ge_input s 12)
  have hFirst := RationalThreeSpecCode.constructionMetadataWork_bound primitive c hPrimitive (i.gluingFirstSpec hcase) _
    hs12 (h.gluingFirst_environment hs hcase)
  have hSecond := RationalThreeSpecCode.constructionMetadataWork_bound primitive c hPrimitive (i.gluingSecondSpec hcase) _
    hs12 (h.gluingSecond_environment hs hcase)
  have hFirstHeight := RationalThreeSpecCode.descriptor_height (i.gluingFirstSpec hcase) _ hs12 (h.gluingFirst_environment hs hcase)
  have hSecondHeight := RationalThreeSpecCode.descriptor_height (i.gluingSecondSpec hcase) _ hs12 (h.gluingSecond_environment hs hcase)
  rw [expressionHeightBudget_comp] at hFirstHeight hSecondHeight
  have hD := (h.scalar hs 1).mono (expressionHeightBudget_mono s (by decide : 12 ≤ 30))
  have hOverlap := RationalOverlapFormula.compilerMetadataWork_bound primitive c hPrimitive (i.overlapData hcase) i.B _
    (hs.trans (expressionHeightBudget_ge_input s 30)) hFirstHeight hSecondHeight hD
    (h.1.mono (expressionHeightBudget_ge_input s 30))
  rw [expressionHeightBudget_comp] at hOverlap
  change RationalOverlapFormula.compilerMetadataWork primitive c (i.overlapData hcase) i.B ≤
    9 * (81 * rationalEnvironmentMetadataBound c 16 (1 + 2 * expressionHeightBudget s 30)) +
      2176 * 81 * RationalExpression.metadataInstructionBound c 16 256 +
        9 * (81 * RationalOverlapFormula.slotIndexMetadataUnitBound c 9 9) +
          PreparedSegmentDescriptor.preparationMetadataBound c 4 81 (expressionHeightBudget s 39) at hOverlap
  unfold gluingConstructionMetadataWork gluingConstructionMetadataBound
  omega

end Blotto.RationalFourInput
