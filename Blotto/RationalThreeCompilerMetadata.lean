import Blotto.RationalExpressionMetadataAllowance
import Blotto.RationalPreparedDescriptorMetadata

/-! The primary regular-three compiler shares one four-word environment.
Selected expression metadata for every weight/endpoint combines with eager
descriptor construction. Formula/environment input production, caller frequency
and physical address/backend/record/ownership/space remain separate. -/

namespace Blotto.RationalThreeGeometryCode
open scoped BigOperators

def expressionMetadataWork (c : ℕ) (g : RationalThreeGeometry) : ℕ :=
  (∑ slot : Fin 9, RationalExpression.metadataAllowance c (chosen slot) (environment g)) +
    (∑ slot : Fin 9, ∑ j : Fin 3, RationalExpression.metadataAllowance c (vertex (RationalThreeGeometry.edges slot).1 j) (environment g)) +
      (∑ slot : Fin 9, ∑ j : Fin 3, RationalExpression.metadataAllowance c (vertex (RationalThreeGeometry.edges slot).2 j) (environment g))

theorem expressionMetadataWork_bound (c : ℕ) (g : RationalThreeGeometry) :
    expressionMetadataWork c g ≤ 2736 * RationalExpression.metadataInstructionBound c 4 256 := by
  let P := RationalExpression.metadataInstructionBound c 4 256
  have hChosen : ∀ slot, RationalExpression.metadataAllowance c (chosen slot) (environment g) ≤ 256 * P :=
    fun slot => RationalExpression.metadataAllowance_uniform_bound c _ _ 4 256 le_rfl (chosen_operationBound slot)
  have hVertex : ∀ i j, RationalExpression.metadataAllowance c (vertex i j) (environment g) ≤ 8 * P := by
    intro i j
    have hCap : (vertex i j).operationBound ≤ 256 := (vertex_operationBound i j).trans (by decide)
    have hUnit := RationalExpression.metadataInstructionBound_mono c (le_refl 4) hCap
    have hCount := vertex_operations g i j
    exact Nat.mul_le_mul hCount hUnit
  have hWeights : (∑ slot : Fin 9, RationalExpression.metadataAllowance c (chosen slot) (environment g)) ≤ 2304 * P := by
    calc
      _ ≤ ∑ _slot : Fin 9, 256 * P := Finset.sum_le_sum (fun slot _ => hChosen slot)
      _ = _ := by simp; ring
  have hLeft : (∑ slot : Fin 9, ∑ j : Fin 3, RationalExpression.metadataAllowance c (vertex (RationalThreeGeometry.edges slot).1 j) (environment g)) ≤ 216 * P := by
    calc
      _ ≤ ∑ _slot : Fin 9, ∑ _j : Fin 3, 8 * P := Finset.sum_le_sum (fun slot _ => Finset.sum_le_sum (fun j _ => hVertex _ j))
      _ = _ := by simp; ring
  have hRight : (∑ slot : Fin 9, ∑ j : Fin 3, RationalExpression.metadataAllowance c (vertex (RationalThreeGeometry.edges slot).2 j) (environment g)) ≤ 216 * P := by
    calc
      _ ≤ ∑ _slot : Fin 9, ∑ _j : Fin 3, 8 * P := Finset.sum_le_sum (fun slot _ => Finset.sum_le_sum (fun j _ => hVertex _ j))
      _ = _ := by simp; ring
  change expressionMetadataWork c g ≤ 2736 * P
  unfold expressionMetadataWork
  omega

def compilerMetadataWork (primitive : ℕ → ℕ) (c : ℕ) (g : RationalThreeGeometry) : ℕ :=
  rationalEnvironmentMetadataWork primitive (environment g) + expressionMetadataWork c g +
    PreparedSegmentDescriptor.preparationMetadataBitWork primitive (compiledLotteryReference g)

theorem compilerMetadataWork_bound (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w)
    (g : RationalThreeGeometry) (s : ℕ) (hs : 2 ≤ s) (hEnv : ∀ j, RationalHeight ((environment g).read j) s) :
    compilerMetadataWork primitive c g ≤ rationalEnvironmentMetadataBound c 4 (1 + 2 * s) +
      2736 * RationalExpression.metadataInstructionBound c 4 256 +
        PreparedSegmentDescriptor.preparationMetadataBound c 3 9 (expressionHeightBudget s 16) := by
  have hEnvironment := rationalEnvironmentMetadataWork_bound primitive c hPrimitive (environment g) _
    (fun j => rationalWordWidth_of_height (hEnv j))
  have hExpressions := expressionMetadataWork_bound c g
  have hDescriptor := PreparedSegmentDescriptor.preparationMetadataBitWork_bound primitive c hPrimitive _ _
    (compiledLotteryReference_height g s hs hEnv)
  exact Nat.add_le_add (Nat.add_le_add hEnvironment hExpressions) hDescriptor

noncomputable def preparedDescriptorWithCompilerMetadataWork (model : RationalCostModel) (primitive : ℕ → ℕ) (c : ℕ)
    (g : RationalThreeGeometry) : ℕ := preparedDescriptorBitCost model g + compilerMetadataWork primitive c g

theorem preparedDescriptorWithCompilerMetadataWork_bound (model : RationalCostModel) (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c * w) (g : RationalThreeGeometry) (s : ℕ) (hs : 2 ≤ s)
    (hEnv : ∀ j, RationalHeight ((environment g).read j) s) :
    preparedDescriptorWithCompilerMetadataWork model primitive c g ≤
      2799 * model.rat (1 + 2 * expressionHeightBudget s 16) +
        (rationalEnvironmentMetadataBound c 4 (1 + 2 * s) + 2736 * RationalExpression.metadataInstructionBound c 4 256 +
          PreparedSegmentDescriptor.preparationMetadataBound c 3 9 (expressionHeightBudget s 16)) :=
  Nat.add_le_add (preparedDescriptorBitCost_bound model g s hs hEnv) (compilerMetadataWork_bound primitive c hPrimitive g s hs hEnv)

end Blotto.RationalThreeGeometryCode
