import Blotto.RationalExpressionMetadataAllowance
import Blotto.RationalNestedResidualPreparation
import Blotto.PreparedDescriptorMetadataWork
import Blotto.RationalPreparationCommonPrice

/-! Residual metadata counts every weight/endpoint formula and its available
environment, then adds written table construction. Environment calls are not
silently shared; child input derivation and caller frequency are separate. -/

namespace Blotto.RationalNestedResidualCode
open scoped BigOperators

def expressionMetadataWork (c : ℕ) (r : RationalNestedResidual) : ℕ :=
  (∑ slot : Fin 3, RationalExpression.metadataAllowance c (weights slot) (environment r)) +
    (∑ slot : Fin 3, ∑ j : Fin 3, RationalExpression.metadataAllowance c (vertices (RationalNestedResidual.edges slot).1 j) (environment r)) +
      (∑ slot : Fin 3, ∑ j : Fin 3, RationalExpression.metadataAllowance c (vertices (RationalNestedResidual.edges slot).2 j) (environment r))

theorem expressionMetadataWork_bound (c : ℕ) (r : RationalNestedResidual) :
    expressionMetadataWork c r ≤ 672 * RationalExpression.metadataInstructionBound c 5 128 := by
  let P := RationalExpression.metadataInstructionBound c 5 128
  have hW : ∀ slot, RationalExpression.metadataAllowance c (weights slot) (environment r) ≤ 128 * P :=
    fun slot => RationalExpression.metadataAllowance_uniform_bound c _ _ 5 128 le_rfl (weight_operationBound slot)
  have hV : ∀ slot j, RationalExpression.metadataAllowance c (vertices slot j) (environment r) ≤ 16 * P := by
    intro slot j
    have hCount := (vertices slot j).run_operations_le (environment r)
    have hCap := vertex_operationBound slot j
    have hUnit := RationalExpression.metadataInstructionBound_mono c (le_refl 5) (hCap.trans (by decide : 16 ≤ 128))
    exact Nat.mul_le_mul (hCount.trans hCap) hUnit
  have hWeights : (∑ slot : Fin 3, RationalExpression.metadataAllowance c (weights slot) (environment r)) ≤ 384 * P := by
    calc
      _ ≤ ∑ _slot : Fin 3, 128 * P := Finset.sum_le_sum (fun slot _ => hW slot)
      _ = _ := by simp; ring
  have hLeft : (∑ slot : Fin 3, ∑ j : Fin 3, RationalExpression.metadataAllowance c (vertices (RationalNestedResidual.edges slot).1 j) (environment r)) ≤ 144 * P := by
    calc
      _ ≤ ∑ _slot : Fin 3, ∑ _j : Fin 3, 16 * P := Finset.sum_le_sum (fun slot _ => Finset.sum_le_sum (fun j _ => hV _ j))
      _ = _ := by simp; ring
  have hRight : (∑ slot : Fin 3, ∑ j : Fin 3, RationalExpression.metadataAllowance c (vertices (RationalNestedResidual.edges slot).2 j) (environment r)) ≤ 144 * P := by
    calc
      _ ≤ ∑ _slot : Fin 3, ∑ _j : Fin 3, 16 * P := Finset.sum_le_sum (fun slot _ => Finset.sum_le_sum (fun j _ => hV _ j))
      _ = _ := by simp; ring
  unfold expressionMetadataWork
  change _ ≤ 672 * P
  omega

def compilerMetadataWork (primitive : ℕ → ℕ) (c : ℕ) (r : RationalNestedResidual) : ℕ :=
  21 * rationalEnvironmentMetadataWork primitive (environment r) + expressionMetadataWork c r +
    PreparedSegmentDescriptor.preparationMetadataBitWork primitive r.segmentLottery

def compilerMetadataBound (c s : ℕ) : ℕ :=
  21 * rationalEnvironmentMetadataBound c 5 (1 + 2 * s) + 672 * RationalExpression.metadataInstructionBound c 5 128 +
    PreparedSegmentDescriptor.preparationMetadataBound c 3 3 (expressionHeightBudget s 8)

theorem compilerMetadataBound_mono (c : ℕ) : Monotone (compilerMetadataBound c) := by
  intro a b hab
  have hEnv := rationalEnvironmentMetadataBound_mono c (le_refl 5) (show 1 + 2 * a ≤ 1 + 2 * b by omega)
  have hTable := PreparedSegmentDescriptor.preparationMetadataBound_mono c (le_refl 3) (le_refl 3)
    (expressionHeightBudget_input_mono hab 8)
  unfold compilerMetadataBound
  gcongr

theorem compilerMetadataWork_bound (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w)
    (r : RationalNestedResidual) (s : ℕ) (hs : 2 ≤ s) (hEnv : ∀ j, RationalHeight ((environment r).read j) s) :
    compilerMetadataWork primitive c r ≤ compilerMetadataBound c s := by
  have hEnvironment := rationalEnvironmentMetadataWork_bound primitive c hPrimitive (environment r) _
    (fun j => rationalWordWidth_of_height (hEnv j))
  have hExpressions := expressionMetadataWork_bound c r
  have hTable := PreparedSegmentDescriptor.preparationMetadataBitWork_bound primitive c hPrimitive _ _ (descriptor_height r s hs hEnv)
  exact Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left 21 hEnvironment) hExpressions) hTable

end Blotto.RationalNestedResidualCode
