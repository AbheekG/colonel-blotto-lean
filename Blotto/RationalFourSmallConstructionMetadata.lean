import Blotto.RationalMergeFourConstructionMetadata
import Blotto.RationalFourSmallPreparation
import Blotto.RationalFourParameterMetadata

/-! Eager small-parent construction metadata prices all scaled and reflected
formula environments and written fields, plus merge/split descriptor production.
Parameter-table multiplicity is supplied by the separate entry ledger. -/

namespace Blotto.RationalFourInput
open scoped BigOperators

def reflectedFields (i : RationalFourInput) (hcase : i.w < (1 - i.p) * i.ell) : FixedArrayTable 10 ℚ :=
  let system := i.reflectedResourceSystem hcase
  FixedArrayTable.ofFn ![system.M, system.long 0, system.long 1, system.long 2,
    system.short 0, system.short 1, system.short 2, system.initial 0, system.initial 1, system.initial 2]

def smallParentConstructionMetadataWork (primitive : ℕ → ℕ) (c : ℕ) (i : RationalFourInput)
    (hcase : i.w < (1 - i.p) * i.ell) : ℕ :=
  (∑ j : Fin 3, (rationalEnvironmentMetadataWork primitive (RationalSmallUniformCode.environment i j) +
    RationalExpression.metadataAllowance c RationalSmallUniformCode.product (RationalSmallUniformCode.environment i j))) +
      rationalEnvironmentMetadataWork primitive (FixedArrayTable.ofFn (i.smallUniformFields hcase)) +
        RationalMergeFourInput.constructionMetadataWork primitive c (i.smallUniformInput hcase) +
          (∑ j : Fin 3, (2 * rationalEnvironmentMetadataWork primitive (RationalReflectedResourceCode.environment i j) +
            RationalExpression.metadataAllowance c RationalReflectedResourceCode.short (RationalReflectedResourceCode.environment i j) +
              RationalExpression.metadataAllowance c RationalReflectedResourceCode.initial (RationalReflectedResourceCode.environment i j))) +
                rationalEnvironmentMetadataWork primitive (i.reflectedFields hcase)

def smallParentConstructionMetadataBound (c s : ℕ) : ℕ :=
  3 * rationalEnvironmentMetadataBound c 2 (1 + 2 * expressionHeightBudget s 12) +
    9 * RationalExpression.metadataInstructionBound c 2 3 +
      rationalEnvironmentMetadataBound c 5 (1 + 2 * expressionHeightBudget s 13) +
        RationalMergeFourInput.constructionMetadataBound c (expressionHeightBudget s 13) +
          6 * rationalEnvironmentMetadataBound c 4 (1 + 2 * expressionHeightBudget s 12) +
            24 * RationalExpression.metadataInstructionBound c 4 5 +
              rationalEnvironmentMetadataBound c 10 (1 + 2 * expressionHeightBudget s 14)

theorem FieldsHeight.smallParentConstructionMetadataWork_bound {i : RationalFourInput} {s : ℕ}
    (h : i.FieldsHeight s) (hs : 2 ≤ s) (hcase : i.w < (1 - i.p) * i.ell)
    (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w) :
    smallParentConstructionMetadataWork primitive c i hcase ≤ smallParentConstructionMetadataBound c s := by
  have hScaled : ∀ j : Fin 3, rationalEnvironmentMetadataWork primitive (RationalSmallUniformCode.environment i j) +
      RationalExpression.metadataAllowance c RationalSmallUniformCode.product (RationalSmallUniformCode.environment i j) ≤
        rationalEnvironmentMetadataBound c 2 (1 + 2 * expressionHeightBudget s 12) +
          3 * RationalExpression.metadataInstructionBound c 2 3 := by
    intro j
    have hScale := h.scalar hs 5
    have hEnv : ∀ k, RationalHeight ((RationalSmallUniformCode.environment i j).read k) (expressionHeightBudget s 12) := by
      intro k
      fin_cases k
      · simpa [RationalSmallUniformCode.environment, FixedArrayTable.read_ofFn, RationalFourParametersCode.values] using hScale
      · simpa [RationalSmallUniformCode.environment, FixedArrayTable.read_ofFn] using
          (h.originalLengths j).mono (expressionHeightBudget_ge_input s 12)
    exact Nat.add_le_add (rationalEnvironmentMetadataWork_bound primitive c hPrimitive _ _
      (fun k => rationalWordWidth_of_height (hEnv k)))
      (RationalExpression.metadataAllowance_uniform_bound c _ _ 2 3 le_rfl (by decide))
  have hScaledSum := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hScaled j)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hScaledSum
  have hInput := h.smallUniformInput hs hcase
  have hFields : ∀ j, RationalHeight ((FixedArrayTable.ofFn (i.smallUniformFields hcase)).read j) (expressionHeightBudget s 13) := by
    intro j
    rw [FixedArrayTable.read_ofFn]
    fin_cases j
    · exact hInput.1
    · exact hInput.2.1
    · exact hInput.2.2.1
    · exact hInput.2.2.2.1
    · exact hInput.2.2.2.2
  have hInputCopy := rationalEnvironmentMetadataWork_bound primitive c hPrimitive _ _
    (fun j => rationalWordWidth_of_height (hFields j))
  have hMerge := hInput.constructionMetadataWork_bound (hs.trans (expressionHeightBudget_ge_input s 13)) primitive c hPrimitive
  have hReflected : ∀ j : Fin 3, 2 * rationalEnvironmentMetadataWork primitive (RationalReflectedResourceCode.environment i j) +
      RationalExpression.metadataAllowance c RationalReflectedResourceCode.short (RationalReflectedResourceCode.environment i j) +
        RationalExpression.metadataAllowance c RationalReflectedResourceCode.initial (RationalReflectedResourceCode.environment i j) ≤
          2 * rationalEnvironmentMetadataBound c 4 (1 + 2 * expressionHeightBudget s 12) +
            8 * RationalExpression.metadataInstructionBound c 4 5 := by
    intro j
    have hEnv := rationalEnvironmentMetadataWork_bound primitive c hPrimitive _ _
      (fun k => rationalWordWidth_of_height (RationalReflectedResourceCode.environment_height h hs j k))
    have hShort := (RationalExpression.metadataAllowance_uniform_bound c RationalReflectedResourceCode.short
      (RationalReflectedResourceCode.environment i j) 4 3 le_rfl (by decide)).trans
      (Nat.mul_le_mul_left 3 (RationalExpression.metadataInstructionBound_mono c (le_refl 4) (by decide : 3 ≤ 5)))
    have hInitial := RationalExpression.metadataAllowance_uniform_bound c RationalReflectedResourceCode.initial
      (RationalReflectedResourceCode.environment i j) 4 5 le_rfl (by decide)
    omega
  have hReflectedSum := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hReflected j)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hReflectedSum
  have hSystem := h.reflectedResourceSystem hs hcase
  have hResourceFields : ∀ j, RationalHeight ((i.reflectedFields hcase).read j) (expressionHeightBudget s 14) := by
    intro j
    fin_cases j
    · simpa [reflectedFields, FixedArrayTable.read_ofFn] using hSystem.1
    · simpa [reflectedFields, FixedArrayTable.read_ofFn] using hSystem.2.1 0
    · simpa [reflectedFields, FixedArrayTable.read_ofFn] using hSystem.2.1 1
    · simpa [reflectedFields, FixedArrayTable.read_ofFn] using hSystem.2.1 2
    · simpa [reflectedFields, FixedArrayTable.read_ofFn] using hSystem.2.2.1 0
    · simpa [reflectedFields, FixedArrayTable.read_ofFn] using hSystem.2.2.1 1
    · simpa [reflectedFields, FixedArrayTable.read_ofFn] using hSystem.2.2.1 2
    · simpa [reflectedFields, FixedArrayTable.read_ofFn] using hSystem.2.2.2 0
    · simpa [reflectedFields, FixedArrayTable.read_ofFn] using hSystem.2.2.2 1
    · simpa [reflectedFields, FixedArrayTable.read_ofFn] using hSystem.2.2.2 2
  have hResourceCopy := rationalEnvironmentMetadataWork_bound primitive c hPrimitive _ _
    (fun j => rationalWordWidth_of_height (hResourceFields j))
  unfold smallParentConstructionMetadataWork smallParentConstructionMetadataBound
  nlinarith

end Blotto.RationalFourInput
