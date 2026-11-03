import Blotto.RationalPreparationCommonPrice

/-! Numerical profile guards price their derived operands and comparisons.
Repeated length/mirror evaluations are retained, rather than assumed cached. -/

namespace Blotto.RationalNestedInput

def lengthFieldProgram (useV : Bool) : RationalNestedParametersCode.Expr :=
  if useV then RationalNestedParametersCode.V else RationalNestedParametersCode.U

def lengthFieldValue (i : RationalNestedInput) (useV : Bool) : ℚ := if useV then i.v else i.u

theorem lengthFieldProgram_value (i : RationalNestedInput) (useV : Bool) :
    (lengthFieldProgram useV).value (RationalNestedParametersCode.environment i 0) = i.lengthFieldValue useV := by
  cases useV <;> simp [lengthFieldProgram, lengthFieldValue]

def lengthFieldBitCost (model : RationalCostModel) (i : RationalNestedInput) (useV : Bool) : ℕ :=
  (lengthFieldProgram useV).bitCost model (RationalNestedParametersCode.environment i 0) +
    rationalWordWidth (i.lengthFieldValue useV)

theorem FieldsHeight.lengthFieldBitCost_bound {i : RationalNestedInput} {s : ℕ} (h : i.FieldsHeight s)
    (hs : 2 ≤ s) (model : RationalCostModel) (useV : Bool) :
    i.lengthFieldBitCost model useV ≤ 4 * model.rat (1 + 2 * expressionHeightBudget s 1) := by
  have hZero : RationalHeight (0 : ℚ) s := (show RationalHeight (0 : ℚ) 2 by norm_num [RationalHeight]).mono hs
  have hEnv := h.environment 0 hZero
  have hLit : (lengthFieldProgram useV).LiteralHeights s := by
    cases useV <;> simp [lengthFieldProgram, RationalNestedParametersCode.U, RationalNestedParametersCode.V,
      RationalNestedParametersCode.M, RationalNestedParametersCode.A, RationalNestedParametersCode.D, RationalExpression.LiteralHeights]
  have hAll := (lengthFieldProgram useV).run_all_heights _ s hEnv hLit
  have hd : (lengthFieldProgram useV).depth = 1 := by cases useV <;> decide
  have ho : (lengthFieldProgram useV).operationBound = 3 := by cases useV <;> decide
  rw [hd] at hAll
  have hc := (lengthFieldProgram useV).bitCost_bound model _ _ hAll
  rw [ho] at hc
  have hv := (lengthFieldProgram useV).run_height _ s hEnv hLit
  change RationalHeight ((lengthFieldProgram useV).value (RationalNestedParametersCode.environment i 0))
    (expressionHeightBudget s (lengthFieldProgram useV).depth) at hv
  rw [lengthFieldProgram_value, hd] at hv
  have hw := (rationalWordWidth_of_height hv).trans (model.word_le _)
  unfold lengthFieldBitCost
  omega

def lengthGuardBitCost (model : RationalCostModel) (i : RationalNestedInput) (useV : Bool) (target : ℚ) : ℕ :=
  i.lengthFieldBitCost model useV + rationalWordWidth (i.lengthFieldValue useV) + rationalWordWidth target +
    model.rat (RationalExpression.pairWidth (i.lengthFieldValue useV) target)

theorem FieldsHeight.lengthGuardBitCost_bound {i : RationalNestedInput} {s : ℕ} (h : i.FieldsHeight s)
    (hs : 2 ≤ s) (model : RationalCostModel) (useV : Bool) (target : ℚ) (ht : RationalHeight target s) :
    i.lengthGuardBitCost model useV target ≤ 7 * model.rat (1 + 2 * expressionHeightBudget s 1) := by
  have hLength : RationalHeight (i.lengthFieldValue useV) (expressionHeightBudget s 1) := by
    cases useV
    · exact h.u
    · exact h.v
  have hTarget := ht.mono (expressionHeightBudget_ge_input s 1)
  have hf := h.lengthFieldBitCost_bound hs model useV
  have hl := (rationalWordWidth_of_height hLength).trans (model.word_le _)
  have ht' := (rationalWordWidth_of_height hTarget).trans (model.word_le _)
  have hp := model.monotone (RationalExpression.pairWidth_height hLength hTarget)
  unfold lengthGuardBitCost
  omega

def mirrorGuardBitCost (model : RationalCostModel) (i : RationalNestedInput) : ℕ :=
  i.scalarFieldBitCost model 0 3 + rationalWordWidth i.mirrorLength + rationalWordWidth i.t +
    model.rat (RationalExpression.pairWidth i.mirrorLength i.t)

theorem FieldsHeight.mirrorGuardBitCost_bound {i : RationalNestedInput} {s : ℕ} (h : i.FieldsHeight s)
    (hs : 2 ≤ s) (model : RationalCostModel) :
    i.mirrorGuardBitCost model ≤ 132 * model.rat (1 + 2 * expressionHeightBudget s 8) := by
  have hZero : RationalHeight (0 : ℚ) s := (show RationalHeight (0 : ℚ) 2 by norm_num [RationalHeight]).mono hs
  have hf := h.scalarFieldBitCost_bound hs model 0 hZero 3
  have hm := h.scalar hs 0 hZero 3
  change RationalHeight i.mirrorLength (expressionHeightBudget s 8) at hm
  have ht := h.2.2.2.2.1.mono (expressionHeightBudget_ge_input s 8)
  have hmw := (rationalWordWidth_of_height hm).trans (model.word_le _)
  have htw := (rationalWordWidth_of_height ht).trans (model.word_le _)
  have hcmp := model.monotone (RationalExpression.pairWidth_height hm ht)
  unfold mirrorGuardBitCost
  omega

end Blotto.RationalNestedInput
