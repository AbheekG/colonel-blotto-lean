import Blotto.RationalFourParameterTableCost
import Blotto.RationalMergeFourPreparation
import Blotto.RationalReflectedResourcePreparation

/-! Small-case preparation constructs the scaled uniform and reflected
resource parents eagerly, as required by the binary-machine start values.
One-time numerical guard/field/table work is explicit; control/root fields,
metadata/backend/ownership and caller repetition remain separate. -/

namespace Blotto.RationalSmallUniformCode
open scoped BigOperators

abbrev Expr := RationalExpression 2
def product : Expr := .mul (.input 0) (.input 1)
def environment (i : RationalFourInput) (j : Fin 3) : FixedArrayTable 2 ℚ :=
  FixedArrayTable.ofFn ![(RationalFourParameterTable.prepare i).scaleFraction, i.originalLengths j]

theorem value_eq (i : RationalFourInput) (j : Fin 3) :
    product.value (environment i j) = i.scaleFraction * i.originalLengths j := by
  simp [product, environment, FixedArrayTable.read_ofFn]

theorem product_bitCost {i : RationalFourInput} {s : ℕ} (h : i.FieldsHeight s) (hs : 2 ≤ s)
    (model : RationalCostModel) (j : Fin 3) :
    product.bitCost model (environment i j) ≤ 3 * model.rat (1 + 2 * expressionHeightBudget s 13) := by
  have hScale := h.scalar hs 5
  have hEnv : ∀ k, RationalHeight ((environment i j).read k) (expressionHeightBudget s 12) := by
    intro k
    fin_cases k
    · simpa [environment, FixedArrayTable.read_ofFn, RationalFourParametersCode.values] using hScale
    · simpa [environment, FixedArrayTable.read_ofFn] using (h.originalLengths j).mono (expressionHeightBudget_ge_input s 12)
  have hLit : product.LiteralHeights (expressionHeightBudget s 12) := by simp [product, RationalExpression.LiteralHeights]
  have hAll := product.run_all_heights _ _ hEnv hLit
  have hd : product.depth = 1 := by decide
  rw [hd] at hAll
  have hp := product.bitCost_bound model _ _ hAll
  have ho : product.operationBound = 3 := by decide
  simpa only [ho, expressionHeightBudget_comp] using hp

def formulaBitCost (model : RationalCostModel) (i : RationalFourInput) : ℕ :=
  ∑ j : Fin 3, product.bitCost model (environment i j)

theorem formulaBitCost_bound {i : RationalFourInput} {s : ℕ} (h : i.FieldsHeight s) (hs : 2 ≤ s) (model : RationalCostModel) :
    formulaBitCost model i ≤ 9 * model.rat (1 + 2 * expressionHeightBudget s 13) := by
  calc
    _ ≤ ∑ _j : Fin 3, 3 * model.rat (1 + 2 * expressionHeightBudget s 13) := Finset.sum_le_sum (fun j _ => product_bitCost h hs model j)
    _ = _ := by simp; ring

end Blotto.RationalSmallUniformCode
namespace Blotto.RationalFourInput
open scoped BigOperators

def smallUniformFields (i : RationalFourInput) (hcase : i.w < (1 - i.p) * i.ell) : Fin 5 → ℚ :=
  let j := i.smallUniformInput hcase
  ![j.B, j.l0, j.l1, j.l2, j.l3]

def smallUniformPayloadBitCost (i : RationalFourInput) (hcase : i.w < (1 - i.p) * i.ell) : ℕ :=
  2 * ∑ j : Fin 5, rationalWordWidth (i.smallUniformFields hcase j)

theorem FieldsHeight.smallUniformPayloadBitCost_bound {i : RationalFourInput} {s : ℕ}
    (h : i.FieldsHeight s) (hs : 2 ≤ s) (hcase : i.w < (1 - i.p) * i.ell) (model : RationalCostModel) :
    i.smallUniformPayloadBitCost hcase ≤ 10 * model.rat (1 + 2 * expressionHeightBudget s 13) := by
  have hInput := h.smallUniformInput hs hcase
  have hFields : ∀ j, RationalHeight (i.smallUniformFields hcase j) (expressionHeightBudget s 13) := by
    intro j
    fin_cases j
    · exact hInput.1
    · exact hInput.2.1
    · exact hInput.2.2.1
    · exact hInput.2.2.2.1
    · exact hInput.2.2.2.2
  have hp : (∑ j : Fin 5, rationalWordWidth (i.smallUniformFields hcase j)) ≤
      5 * model.rat (1 + 2 * expressionHeightBudget s 13) := by
    calc
      _ ≤ ∑ _j : Fin 5, model.rat (1 + 2 * expressionHeightBudget s 13) := Finset.sum_le_sum (fun j _ =>
        (rationalWordWidth_of_height (hFields j)).trans (model.word_le _))
      _ = _ := by simp
  unfold smallUniformPayloadBitCost
  omega

def smallUniformInputPreparationBitCost (model : RationalCostModel) (i : RationalFourInput)
    (hcase : i.w < (1 - i.p) * i.ell) : ℕ :=
  RationalFourParameterTable.preparationBitCost model i + RationalSmallUniformCode.formulaBitCost model i +
    i.smallUniformPayloadBitCost hcase

theorem FieldsHeight.smallUniformInputPreparationBitCost_bound {i : RationalFourInput} {s : ℕ}
    (h : i.FieldsHeight s) (hs : 2 ≤ s) (hcase : i.w < (1 - i.p) * i.ell) (model : RationalCostModel) :
    i.smallUniformInputPreparationBitCost model hcase ≤ 2087 * model.rat (1 + 2 * expressionHeightBudget s 13) := by
  have hp := (RationalFourParameterTable.preparationBitCost_bound h hs model).trans (Nat.mul_le_mul_left 2068
    (model.heightPrice_mono (le_refl s) (by decide : 12 ≤ 13)))
  have hf := RationalSmallUniformCode.formulaBitCost_bound h hs model
  have hw := h.smallUniformPayloadBitCost_bound hs hcase model
  unfold smallUniformInputPreparationBitCost
  omega

noncomputable def smallUniformPreparationAllowance (model : RationalCostModel) (i : RationalFourInput)
    (hcase : i.w < (1 - i.p) * i.ell) : ℕ :=
  i.smallUniformInputPreparationBitCost model hcase + (i.smallUniformInput hcase).preparedDescriptorAllowance model

theorem FieldsHeight.smallUniformPreparationAllowance_bound {i : RationalFourInput} {s : ℕ}
    (h : i.FieldsHeight s) (hs : 2 ≤ s) (hcase : i.w < (1 - i.p) * i.ell) (model : RationalCostModel) :
    i.smallUniformPreparationAllowance model hcase ≤ 15302 * model.rat (1 + 2 * expressionHeightBudget s 35) := by
  have hInput := (h.smallUniformInputPreparationBitCost_bound hs hcase model).trans (Nat.mul_le_mul_left 2087
    (model.heightPrice_mono (le_refl s) (by decide : 13 ≤ 35)))
  have hDesc := (h.smallUniformInput hs hcase).preparedDescriptorAllowance_bound
    (hs.trans (expressionHeightBudget_ge_input s 13)) model
  rw [expressionHeightBudget_comp] at hDesc
  change (i.smallUniformInput hcase).preparedDescriptorAllowance model ≤
    13215 * model.rat (1 + 2 * expressionHeightBudget s 35) at hDesc
  unfold smallUniformPreparationAllowance
  omega

noncomputable def smallParentPreparationAllowance (model : RationalCostModel) (i : RationalFourInput)
    (hcase : i.w < (1 - i.p) * i.ell) : ℕ :=
  i.smallUniformPreparationAllowance model hcase + i.reflectedResourcePreparationBitCost model hcase

theorem FieldsHeight.smallParentPreparationAllowance_bound {i : RationalFourInput} {s : ℕ}
    (h : i.FieldsHeight s) (hs : 2 ≤ s) (hcase : i.w < (1 - i.p) * i.ell) (model : RationalCostModel) :
    i.smallParentPreparationAllowance model hcase ≤ 17414 * model.rat (1 + 2 * expressionHeightBudget s 35) := by
  have hUniform := h.smallUniformPreparationAllowance_bound hs hcase model
  have hResource := (h.reflectedResourcePreparationBitCost_bound hs hcase model).trans (Nat.mul_le_mul_left 2112
    (model.heightPrice_mono (le_refl s) (by decide : 14 ≤ 35)))
  unfold smallParentPreparationAllowance
  omega

end Blotto.RationalFourInput
