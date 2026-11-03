import Blotto.RationalExpressionMetadataAllowance
import Blotto.RationalFourParameterTableCost

/-! One primary eight-entry parameter-table construction includes its actual
input environment, selected expression counters/control and full-prefix result
buffer copies. Caller multiplicity and physical addresses/backend/records/
ownership/space remain separate. -/

namespace Blotto.RationalFourParameterTable
open scoped BigOperators

def preparationMetadataWork (primitive : ℕ → ℕ) (c : ℕ) (i : RationalFourInput) : ℕ :=
  rationalEnvironmentMetadataWork primitive (RationalFourParametersCode.environment i) +
    (∑ j : Fin 8, RationalExpression.metadataAllowance c (RationalFourParametersCode.programs j) (RationalFourParametersCode.environment i)) +
      rationalArrayCopyWork (List.ofFn (prepare i).table.read) 0 + indexedLoopMetadataBitWork primitive 0 8

def preparationMetadataBound (c s : ℕ) : ℕ :=
  rationalEnvironmentMetadataBound c 6 (1 + 2 * s) + 2048 * RationalExpression.metadataInstructionBound c 6 256 +
    128 * (1 + 2 * expressionHeightBudget s 12) + indexedLoopMetadataBound c 8

theorem preparationMetadataWork_bound (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w)
    {i : RationalFourInput} {s : ℕ} (h : i.FieldsHeight s) (hs : 2 ≤ s) :
    preparationMetadataWork primitive c i ≤ preparationMetadataBound c s := by
  have hEnv := rationalEnvironmentMetadataWork_bound primitive c hPrimitive (RationalFourParametersCode.environment i)
    (1 + 2 * s) (fun j => rationalWordWidth_of_height (h.environment j))
  have hPrograms : (∑ j : Fin 8, RationalExpression.metadataAllowance c (RationalFourParametersCode.programs j) (RationalFourParametersCode.environment i)) ≤
      2048 * RationalExpression.metadataInstructionBound c 6 256 := by
    calc
      _ ≤ ∑ _j : Fin 8, 256 * RationalExpression.metadataInstructionBound c 6 256 := Finset.sum_le_sum (fun j _ =>
        RationalExpression.metadataAllowance_uniform_bound c _ _ 6 256 le_rfl (RationalFourParametersCode.operationBound j))
      _ = _ := by simp; ring
  have hFields : ∀ j, rationalWordWidth ((prepare i).table.read j) ≤ 1 + 2 * expressionHeightBudget s 12 := by
    intro j
    rw [(prepare i).correct]
    exact rationalWordWidth_of_height (h.scalar hs j)
  have hWords := rationalWordWidth_sum_bound (List.ofFn (prepare i).table.read) (1 + 2 * expressionHeightBudget s 12)
    (by intro q hq; rcases List.mem_ofFn.mp hq with ⟨j, rfl⟩; exact hFields j)
  have hCopy := rationalArrayCopyWork_bound (List.ofFn (prepare i).table.read) 0
  simp only [List.length_ofFn, Nat.zero_add] at hWords hCopy
  have hCopyPrice : rationalArrayCopyWork (List.ofFn (prepare i).table.read) 0 ≤ 128 * (1 + 2 * expressionHeightBudget s 12) := by
    have h := hCopy.trans (Nat.mul_le_mul_left 16 hWords)
    nlinarith
  have hLoop := indexedLoopMetadataBitWork_bound primitive c hPrimitive 8
  unfold preparationMetadataWork preparationMetadataBound
  omega

noncomputable def preparationWithMetadataWork (model : RationalCostModel) (primitive : ℕ → ℕ) (c : ℕ) (i : RationalFourInput) : ℕ :=
  preparationBitCost model i + preparationMetadataWork primitive c i

theorem preparationWithMetadataWork_bound (model : RationalCostModel) (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c * w) {i : RationalFourInput} {s : ℕ} (h : i.FieldsHeight s) (hs : 2 ≤ s) :
    preparationWithMetadataWork model primitive c i ≤ 2068 * model.rat (1 + 2 * expressionHeightBudget s 12) + preparationMetadataBound c s :=
  Nat.add_le_add (preparationBitCost_bound h hs model) (preparationMetadataWork_bound primitive c hPrimitive h hs)

end Blotto.RationalFourParameterTable
