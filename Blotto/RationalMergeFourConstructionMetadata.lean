import Blotto.RationalMergeFourPreparation
import Blotto.RationalThreeSpecConstructionMetadata

/-! Merge/split metadata retains every dense row environment and formula,
the final written table, and the existing four child-production allowances.
These are labelled construction components, separate from physical ownership. -/

namespace Blotto.RationalSplitCode
open scoped BigOperators

def descriptorMetadataWork (primitive : ℕ → ℕ) (c : ℕ) (a d : ℚ) (l : RationalSegmentLottery 3 9) : ℕ :=
  (∑ slot : Fin 9, ∑ j : Fin 4, (rationalEnvironmentMetadataWork primitive (environment a d (l.P slot)) +
    RationalExpression.metadataAllowance c (row j) (environment a d (l.P slot)))) +
      (∑ slot : Fin 9, ∑ j : Fin 4, (rationalEnvironmentMetadataWork primitive (environment a d (l.Q slot)) +
        RationalExpression.metadataAllowance c (row j) (environment a d (l.Q slot)))) +
          PreparedSegmentDescriptor.preparationMetadataBitWork primitive (l.mapped (RationalAffineAllocation.splitFirstTwo a d))

def descriptorMetadataBound (c s : ℕ) : ℕ :=
  72 * rationalEnvironmentMetadataBound c 5 (1 + 2 * s) +
    1440 * RationalExpression.metadataInstructionBound c 5 20 +
      PreparedSegmentDescriptor.preparationMetadataBound c 4 9 (expressionHeightBudget s 3)

theorem descriptorMetadataWork_bound (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w)
    (a d : ℚ) (l : RationalSegmentLottery 3 9) (s : ℕ) (hA : RationalHeight a s) (hD : RationalHeight d s)
    (h : l.HeightAt s) : descriptorMetadataWork primitive c a d l ≤ descriptorMetadataBound c s := by
  let unit := rationalEnvironmentMetadataBound c 5 (1 + 2 * s) + 20 * RationalExpression.metadataInstructionBound c 5 20
  have hRow : ∀ (x : Fin 3 → ℚ), (∀ k, RationalHeight (x k) s) → ∀ j : Fin 4,
      rationalEnvironmentMetadataWork primitive (environment a d x) +
        RationalExpression.metadataAllowance c (row j) (environment a d x) ≤ unit := by
    intro x hx j
    have hEnv : ∀ k, RationalHeight ((environment a d x).read k) s := by
      intro k
      fin_cases k
      · simpa [environment, FixedArrayTable.read_ofFn] using hA
      · simpa [environment, FixedArrayTable.read_ofFn] using hD
      · simpa [environment, FixedArrayTable.read_ofFn] using hx 0
      · simpa [environment, FixedArrayTable.read_ofFn] using hx 1
      · simpa [environment, FixedArrayTable.read_ofFn] using hx 2
    exact Nat.add_le_add (rationalEnvironmentMetadataWork_bound primitive c hPrimitive _ _
      (fun k => rationalWordWidth_of_height (hEnv k)))
      (RationalExpression.metadataAllowance_uniform_bound c _ _ 5 20 le_rfl (row_operations j))
  have hP : (∑ slot : Fin 9, ∑ j : Fin 4, (rationalEnvironmentMetadataWork primitive (environment a d (l.P slot)) +
      RationalExpression.metadataAllowance c (row j) (environment a d (l.P slot)))) ≤ 36 * unit := by
    calc
      _ ≤ ∑ _slot : Fin 9, ∑ _j : Fin 4, unit := Finset.sum_le_sum (fun slot _ =>
        Finset.sum_le_sum (fun j _ => hRow _ (fun k => (h.2 slot k).1) j))
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]; ring
  have hQ : (∑ slot : Fin 9, ∑ j : Fin 4, (rationalEnvironmentMetadataWork primitive (environment a d (l.Q slot)) +
      RationalExpression.metadataAllowance c (row j) (environment a d (l.Q slot)))) ≤ 36 * unit := by
    calc
      _ ≤ ∑ _slot : Fin 9, ∑ _j : Fin 4, unit := Finset.sum_le_sum (fun slot _ =>
        Finset.sum_le_sum (fun j _ => hRow _ (fun k => (h.2 slot k).2) j))
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]; ring
  have hTable := PreparedSegmentDescriptor.preparationMetadataBitWork_bound primitive c hPrimitive _ _ (h.mapped_split a d hA hD)
  unfold descriptorMetadataWork descriptorMetadataBound
  dsimp [unit] at hP hQ
  omega

end Blotto.RationalSplitCode

namespace Blotto.RationalMergeFourInput

def constructionMetadataWork (primitive : ℕ → ℕ) (c : ℕ) (i : RationalMergeFourInput) : ℕ :=
  rationalEnvironmentMetadataWork primitive (RationalLotteryAssemblyCode.environment i.l0 i.l1) +
    RationalExpression.metadataAllowance c RationalLotteryAssemblyCode.sum (RationalLotteryAssemblyCode.environment i.l0 i.l1) +
      4 * RationalThreeSpecCode.constructionMetadataWork primitive c i.childSpec +
        RationalSplitCode.descriptorMetadataWork primitive c i.l0 i.l1 i.childSpec.segmentLottery

def constructionMetadataBound (c s : ℕ) : ℕ :=
  rationalEnvironmentMetadataBound c 2 (1 + 2 * s) + 3 * RationalExpression.metadataInstructionBound c 2 3 +
    4 * RationalThreeSpecCode.constructionMetadataBound c (expressionHeightBudget s 1) +
      RationalSplitCode.descriptorMetadataBound c (expressionHeightBudget s 19)

theorem FieldsHeight.constructionMetadataWork_bound {i : RationalMergeFourInput} {s : ℕ}
    (h : i.FieldsHeight s) (hs : 2 ≤ s) (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w) :
    constructionMetadataWork primitive c i ≤ constructionMetadataBound c s := by
  have hEnv := RationalLotteryAssemblyCode.environmentMetadataWork_bound primitive c hPrimitive i.l0 i.l1 s h.2.1 h.2.2.1
  have hSum := RationalExpression.metadataAllowance_uniform_bound c RationalLotteryAssemblyCode.sum
    (RationalLotteryAssemblyCode.environment i.l0 i.l1) 2 3 le_rfl (by decide)
  have hChild := RationalThreeSpecCode.constructionMetadataWork_bound primitive c hPrimitive i.childSpec _
    (hs.trans (expressionHeightBudget_ge_input s 1)) (h.child_environment hs)
  have hHeight := RationalThreeSpecCode.descriptor_height i.childSpec _
    (hs.trans (expressionHeightBudget_ge_input s 1)) (h.child_environment hs)
  rw [expressionHeightBudget_comp] at hHeight
  have hSplit := RationalSplitCode.descriptorMetadataWork_bound primitive c hPrimitive i.l0 i.l1 i.childSpec.segmentLottery _
    (h.2.1.mono (expressionHeightBudget_ge_input s 19)) (h.2.2.1.mono (expressionHeightBudget_ge_input s 19)) hHeight
  exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hEnv hSum) (Nat.mul_le_mul_left 4 hChild)) hSplit

end Blotto.RationalMergeFourInput
