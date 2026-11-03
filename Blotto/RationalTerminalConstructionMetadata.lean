import Blotto.RationalNestedSpecConstructionMetadata
import Blotto.RationalTerminalResourcePreparation

/-! Terminal preparation retains repeated focus environments, the fractional
weight, written nested fields, three child construction prices and dense
permutation metadata. This is one factory price; invocation counts are separate. -/

namespace Blotto.RationalTerminalResources
open scoped BigOperators

def inputConstructionMetadataWork (primitive : ℕ → ℕ) (c : ℕ) (i : RationalTerminalResources) : ℕ :=
  6 * (∑ j : Fin 2, (rationalEnvironmentMetadataWork primitive (RationalTerminalResourceCode.environment i (j.castLE (by decide))) +
    RationalExpression.metadataAllowance c RationalTerminalResourceCode.capacity (RationalTerminalResourceCode.environment i (j.castLE (by decide))))) +
      rationalEnvironmentMetadataWork primitive (RationalTerminalResourceCode.environment i i.focus) +
        RationalExpression.metadataAllowance c RationalTerminalResourceCode.weight (RationalTerminalResourceCode.environment i i.focus) +
          RationalNestedSpec.sortingFieldsMetadataWork primitive i.input

def inputConstructionMetadataBound (c s : ℕ) : ℕ :=
  13 * rationalEnvironmentMetadataBound c 3 (1 + 2 * s) + 36 * RationalExpression.metadataInstructionBound c 3 3 +
    6 * RationalExpression.metadataInstructionBound c 3 6 + RationalNestedSpec.sortingFieldsMetadataBound c (expressionHeightBudget s 2)

theorem FieldsHeight.inputConstructionMetadataWork_bound {i : RationalTerminalResources} {s : ℕ} (h : i.FieldsHeight s)
    (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w) :
    inputConstructionMetadataWork primitive c i ≤ inputConstructionMetadataBound c s := by
  have hEnv : ∀ j, rationalEnvironmentMetadataWork primitive (RationalTerminalResourceCode.environment i j) ≤
      rationalEnvironmentMetadataBound c 3 (1 + 2 * s) := by
    intro j
    exact rationalEnvironmentMetadataWork_bound primitive c hPrimitive _ _
      (fun k => rationalWordWidth_of_height (RationalTerminalResourceCode.environment_height h j k))
  have hCapacity : ∀ j, RationalExpression.metadataAllowance c RationalTerminalResourceCode.capacity (RationalTerminalResourceCode.environment i j) ≤
      3 * RationalExpression.metadataInstructionBound c 3 3 := fun j =>
    RationalExpression.metadataAllowance_uniform_bound c _ _ 3 3 le_rfl (by decide)
  have hFocus : (∑ j : Fin 2, (rationalEnvironmentMetadataWork primitive (RationalTerminalResourceCode.environment i (j.castLE (by decide))) +
      RationalExpression.metadataAllowance c RationalTerminalResourceCode.capacity (RationalTerminalResourceCode.environment i (j.castLE (by decide))))) ≤
      2 * (rationalEnvironmentMetadataBound c 3 (1 + 2 * s) + 3 * RationalExpression.metadataInstructionBound c 3 3) := by
    calc
      _ ≤ ∑ _j : Fin 2, (rationalEnvironmentMetadataBound c 3 (1 + 2 * s) + 3 * RationalExpression.metadataInstructionBound c 3 3) :=
        Finset.sum_le_sum (fun j _ => Nat.add_le_add (hEnv _) (hCapacity _))
      _ = _ := by simp
  have hWeight := RationalExpression.metadataAllowance_uniform_bound c RationalTerminalResourceCode.weight
    (RationalTerminalResourceCode.environment i i.focus) 3 6 le_rfl (by decide)
  have hFields := h.input.sortingFieldsMetadataWork_bound primitive c hPrimitive
  have hSelected := hEnv i.focus
  unfold inputConstructionMetadataWork inputConstructionMetadataBound
  nlinarith

def profileConstructionMetadataWork (primitive : ℕ → ℕ) (c : ℕ) (i : RationalTerminalResources) (K : ℕ) (bits : Fin K → Bool) : ℕ :=
  inputConstructionMetadataWork primitive c i + 3 * RationalNestedSpec.profileConstructionMetadataWork primitive c i.input K bits +
    RationalPermutationCode.descriptorMetadataWork primitive c (i.input.profile K bits) i.permutation

def profileConstructionMetadataBound (c s K : ℕ) : ℕ :=
  inputConstructionMetadataBound c s + 3 * RationalNestedSpec.profileConstructionMetadataBound c (expressionHeightBudget s 2) K +
    RationalPermutationCode.descriptorMetadataBound c (expressionHeightBudget s 47)

theorem profileConstructionMetadataBound_mono (c : ℕ) {s t K L : ℕ} (hs : s ≤ t) (hK : K ≤ L) :
    profileConstructionMetadataBound c s K ≤ profileConstructionMetadataBound c t L := by
  have hEnv := rationalEnvironmentMetadataBound_mono c (le_refl 3) (show 1 + 2 * s ≤ 1 + 2 * t by omega)
  have hFields : RationalNestedSpec.sortingFieldsMetadataBound c (expressionHeightBudget s 2) ≤ RationalNestedSpec.sortingFieldsMetadataBound c (expressionHeightBudget t 2) := by
    have h := expressionHeightBudget_input_mono hs 2
    unfold RationalNestedSpec.sortingFieldsMetadataBound
    omega
  have hInput : inputConstructionMetadataBound c s ≤ inputConstructionMetadataBound c t := by
    unfold inputConstructionMetadataBound
    gcongr
  have hChild := RationalNestedSpec.profileConstructionMetadataBound_mono c (expressionHeightBudget_input_mono hs 2) hK
  have hPermutation := RationalPermutationCode.descriptorMetadataBound_mono c (expressionHeightBudget_input_mono hs 47)
  unfold profileConstructionMetadataBound
  gcongr

theorem FieldsHeight.profileConstructionMetadataWork_common {i : RationalTerminalResources} {s : ℕ} (h : i.FieldsHeight s) (hs : 2 ≤ s)
    (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w) (K : ℕ) (hK : K + 2 ≤ s) (bits : Fin K → Bool) :
    profileConstructionMetadataWork primitive c i K bits ≤ profileConstructionMetadataBound c s K := by
  have hInput := h.inputConstructionMetadataWork_bound primitive c hPrimitive
  have hLevel := expressionHeightBudget_ge_input s 2
  have hChild := h.input.profileConstructionMetadataWork_common (hs.trans hLevel) primitive c hPrimitive K (hK.trans hLevel) bits
  have hProfile := h.input.profile (hs.trans hLevel) K bits
  rw [max_eq_left (hK.trans hLevel), expressionHeightBudget_comp] at hProfile
  have hPermutation := RationalPermutationCode.descriptorMetadataWork_bound primitive c hPrimitive _ i.permutation _ hProfile
  change RationalPermutationCode.descriptorMetadataWork primitive c (i.input.profile K bits) i.permutation ≤
    RationalPermutationCode.descriptorMetadataBound c (expressionHeightBudget s 47) at hPermutation
  exact Nat.add_le_add (Nat.add_le_add hInput (Nat.mul_le_mul_left 3 hChild)) hPermutation

theorem FieldsHeight.profileConstructionMetadataWork_bound {i : RationalTerminalResources} {s : ℕ} (h : i.FieldsHeight s) (hs : 2 ≤ s)
    (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w) (K : ℕ) (bits : Fin K → Bool) :
    profileConstructionMetadataWork primitive c i K bits ≤ profileConstructionMetadataBound c (max s (K + 2)) K :=
  (h.mono (le_max_left _ _)).profileConstructionMetadataWork_common (hs.trans (le_max_left _ _))
    primitive c hPrimitive K (le_max_right _ _) bits

end Blotto.RationalTerminalResources
