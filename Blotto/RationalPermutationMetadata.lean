import Blotto.RationalThreeSpecConstructionMetadata
import Blotto.RationalPermutationPreparation

/-! Dense three-coordinate permutation evaluates every product, including
zero coefficients. Every endpoint row environment and selected-expression
counter/control price is retained before full final table construction. -/

namespace Blotto.RationalPermutationCode
open scoped BigOperators

def descriptorMetadataWork (primitive : ℕ → ℕ) (c : ℕ) (l : RationalSegmentLottery 3 18) (π : Equiv.Perm (Fin 3)) : ℕ :=
  3 * (∑ slot : Fin 18, (rationalEnvironmentMetadataWork primitive (environment (l.P slot)) +
    rationalEnvironmentMetadataWork primitive (environment (l.Q slot)))) +
    (∑ slot : Fin 18, ∑ j : Fin 3, RationalExpression.metadataAllowance c (row (π j)) (environment (l.P slot))) +
      (∑ slot : Fin 18, ∑ j : Fin 3, RationalExpression.metadataAllowance c (row (π j)) (environment (l.Q slot))) +
        PreparedSegmentDescriptor.preparationMetadataBitWork primitive (l.mapped (RationalAffineAllocation.permutation π))

def descriptorMetadataBound (c s : ℕ) : ℕ :=
  108 * rationalEnvironmentMetadataBound c 3 (1 + 2 * s) + 1620 * RationalExpression.metadataInstructionBound c 3 15 +
    PreparedSegmentDescriptor.preparationMetadataBound c 3 18 s

theorem descriptorMetadataBound_mono (c : ℕ) : Monotone (descriptorMetadataBound c) := by
  intro a b hab
  have hEnv := rationalEnvironmentMetadataBound_mono c (le_refl 3) (show 1 + 2 * a ≤ 1 + 2 * b by omega)
  have hTable := PreparedSegmentDescriptor.preparationMetadataBound_mono c (le_refl 3) (le_refl 18) hab
  unfold descriptorMetadataBound
  gcongr

theorem descriptorMetadataWork_bound (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w)
    (l : RationalSegmentLottery 3 18) (π : Equiv.Perm (Fin 3)) (s : ℕ) (h : l.HeightAt s) :
    descriptorMetadataWork primitive c l π ≤ descriptorMetadataBound c s := by
  have hEnv : (∑ slot : Fin 18, (rationalEnvironmentMetadataWork primitive (environment (l.P slot)) +
      rationalEnvironmentMetadataWork primitive (environment (l.Q slot)))) ≤ 36 * rationalEnvironmentMetadataBound c 3 (1 + 2 * s) := by
    calc
      _ ≤ ∑ _slot : Fin 18, 2 * rationalEnvironmentMetadataBound c 3 (1 + 2 * s) := Finset.sum_le_sum (fun slot _ => by
        have hp := rationalEnvironmentMetadataWork_bound primitive c hPrimitive (environment (l.P slot)) _
          (by intro j; simpa [environment, FixedArrayTable.read_ofFn] using rationalWordWidth_of_height (h.2 slot j).1)
        have hq := rationalEnvironmentMetadataWork_bound primitive c hPrimitive (environment (l.Q slot)) _
          (by intro j; simpa [environment, FixedArrayTable.read_ofFn] using rationalWordWidth_of_height (h.2 slot j).2)
        omega)
      _ = _ := by simp; ring
  have hExpr : ∀ k x, RationalExpression.metadataAllowance c (row k) (environment x) ≤ 15 * RationalExpression.metadataInstructionBound c 3 15 :=
    fun k x => RationalExpression.metadataAllowance_uniform_bound c _ _ 3 15 le_rfl (row_operations k)
  have hLeft : (∑ slot : Fin 18, ∑ j : Fin 3, RationalExpression.metadataAllowance c (row (π j)) (environment (l.P slot))) ≤
      810 * RationalExpression.metadataInstructionBound c 3 15 := by
    calc
      _ ≤ ∑ _slot : Fin 18, ∑ _j : Fin 3, 15 * RationalExpression.metadataInstructionBound c 3 15 :=
        Finset.sum_le_sum (fun slot _ => Finset.sum_le_sum (fun j _ => hExpr _ _))
      _ = _ := by simp; ring
  have hRight : (∑ slot : Fin 18, ∑ j : Fin 3, RationalExpression.metadataAllowance c (row (π j)) (environment (l.Q slot))) ≤
      810 * RationalExpression.metadataInstructionBound c 3 15 := by
    calc
      _ ≤ ∑ _slot : Fin 18, ∑ _j : Fin 3, 15 * RationalExpression.metadataInstructionBound c 3 15 :=
        Finset.sum_le_sum (fun slot _ => Finset.sum_le_sum (fun j _ => hExpr _ _))
      _ = _ := by simp; ring
  have hTable := PreparedSegmentDescriptor.preparationMetadataBitWork_bound primitive c hPrimitive _ _ (h.mapped_permutation π)
  unfold descriptorMetadataWork descriptorMetadataBound
  omega

end Blotto.RationalPermutationCode
