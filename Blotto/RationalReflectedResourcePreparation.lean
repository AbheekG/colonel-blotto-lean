import Blotto.RationalFourParameterTableCost
import Blotto.RationalFourSmallHeight

/-! The actual reflected-resource factory reads its prepared parameters,
forms short/initial coordinates and stores ten rational fields. One factory
invocation is priced; initial active-list/reader setup and backend are separate. -/

namespace Blotto.RationalReflectedResourceCode
open scoped BigOperators

abbrev Expr := RationalExpression 4
def short : Expr := .mul (.input 0) (.input 3)
def initial : Expr := .mul (.mul (.input 1) (.input 2)) (.input 3)
def environment (i : RationalFourInput) (j : Fin 3) : FixedArrayTable 4 ℚ :=
  let p := RationalFourParameterTable.prepare i
  FixedArrayTable.ofFn ![p.shortFraction, p.nestedProbability, p.scaleFraction, i.originalLengths j]

theorem short_value (i : RationalFourInput) (hcase : i.w < (1 - i.p) * i.ell) (j : Fin 3) :
    short.value (environment i j) = (i.reflectedResourceSystem hcase).short j := by
  simp [short, environment, FixedArrayTable.read_ofFn, RationalFourInput.reflectedResourceSystem]

theorem initial_value (i : RationalFourInput) (hcase : i.w < (1 - i.p) * i.ell) (j : Fin 3) :
    initial.value (environment i j) = (i.reflectedResourceSystem hcase).initial j := by
  simp [initial, environment, FixedArrayTable.read_ofFn, RationalFourInput.reflectedResourceSystem]

theorem environment_height {i : RationalFourInput} {s : ℕ} (h : i.FieldsHeight s) (hs : 2 ≤ s) (j : Fin 3) :
    ∀ k, RationalHeight ((environment i j).read k) (expressionHeightBudget s 12) := by
  have hShort := h.scalar hs 4
  have hProbability := h.scalar hs 6
  have hScale := h.scalar hs 5
  intro k
  fin_cases k
  · simpa [environment, FixedArrayTable.read_ofFn, RationalFourParametersCode.values] using hShort
  · simpa [environment, FixedArrayTable.read_ofFn, RationalFourParametersCode.values] using hProbability
  · simpa [environment, FixedArrayTable.read_ofFn, RationalFourParametersCode.values] using hScale
  · simpa [environment, FixedArrayTable.read_ofFn] using (h.originalLengths j).mono (expressionHeightBudget_ge_input s 12)

theorem short_bitCost {i : RationalFourInput} {s : ℕ} (h : i.FieldsHeight s) (hs : 2 ≤ s)
    (model : RationalCostModel) (j : Fin 3) :
    short.bitCost model (environment i j) ≤ 3 * model.rat (1 + 2 * expressionHeightBudget s 14) := by
  have hLit : short.LiteralHeights (expressionHeightBudget s 12) := by simp [short, RationalExpression.LiteralHeights]
  have hAll := short.run_all_heights _ _ (environment_height h hs j) hLit
  have hd : short.depth ≤ 2 := by decide
  have hm := expressionHeightBudget_mono (expressionHeightBudget s 12) hd
  have hp := short.bitCost_bound model _ _ (RationalExpression.AllRunHeights_mono _ _ hm hAll)
  have ho : short.operationBound = 3 := by decide
  simpa only [ho, expressionHeightBudget_comp] using hp

theorem initial_bitCost {i : RationalFourInput} {s : ℕ} (h : i.FieldsHeight s) (hs : 2 ≤ s)
    (model : RationalCostModel) (j : Fin 3) :
    initial.bitCost model (environment i j) ≤ 5 * model.rat (1 + 2 * expressionHeightBudget s 14) := by
  have hLit : initial.LiteralHeights (expressionHeightBudget s 12) := by simp [initial, RationalExpression.LiteralHeights]
  have hAll := initial.run_all_heights _ _ (environment_height h hs j) hLit
  have hd : initial.depth = 2 := by decide
  rw [hd] at hAll
  have hp := initial.bitCost_bound model _ _ hAll
  have ho : initial.operationBound = 5 := by decide
  simpa only [ho, expressionHeightBudget_comp] using hp

def formulaBitCost (model : RationalCostModel) (i : RationalFourInput) : ℕ :=
  ∑ j : Fin 3, (short.bitCost model (environment i j) + initial.bitCost model (environment i j))

theorem formulaBitCost_bound {i : RationalFourInput} {s : ℕ} (h : i.FieldsHeight s) (hs : 2 ≤ s) (model : RationalCostModel) :
    formulaBitCost model i ≤ 24 * model.rat (1 + 2 * expressionHeightBudget s 14) := by
  have hp : ∀ j : Fin 3, short.bitCost model (environment i j) + initial.bitCost model (environment i j) ≤
      8 * model.rat (1 + 2 * expressionHeightBudget s 14) := by
    intro j
    have hS := short_bitCost h hs model j
    have hI := initial_bitCost h hs model j
    omega
  calc
    _ ≤ ∑ _j : Fin 3, 8 * model.rat (1 + 2 * expressionHeightBudget s 14) := Finset.sum_le_sum (fun j _ => hp j)
    _ = _ := by simp; ring

end Blotto.RationalReflectedResourceCode
namespace Blotto.RationalFourInput
open scoped BigOperators

def reflectedResourcePayloadBitCost (i : RationalFourInput) (hcase : i.w < (1 - i.p) * i.ell) : ℕ :=
  let system := i.reflectedResourceSystem hcase
  2 * (rationalWordWidth system.M + (∑ j, rationalWordWidth (system.long j)) +
    (∑ j, rationalWordWidth (system.short j)) + ∑ j, rationalWordWidth (system.initial j))

theorem FieldsHeight.reflectedResourcePayloadBitCost_bound {i : RationalFourInput} {s : ℕ}
    (h : i.FieldsHeight s) (hs : 2 ≤ s) (hcase : i.w < (1 - i.p) * i.ell) (model : RationalCostModel) :
    i.reflectedResourcePayloadBitCost hcase ≤ 20 * model.rat (1 + 2 * expressionHeightBudget s 14) := by
  have hSystem := h.reflectedResourceSystem hs hcase
  let system := i.reflectedResourceSystem hcase
  let price := model.rat (1 + 2 * expressionHeightBudget s 14)
  have hM := (rationalWordWidth_of_height hSystem.1).trans (model.word_le _)
  change rationalWordWidth system.M ≤ price at hM
  have hLong : (∑ j : Fin 3, rationalWordWidth (system.long j)) ≤ 3 * price := by
    calc
      _ ≤ ∑ _j : Fin 3, price := Finset.sum_le_sum (fun j _ => (rationalWordWidth_of_height (hSystem.2.1 j)).trans (model.word_le _))
      _ = _ := by simp
  have hShort : (∑ j : Fin 3, rationalWordWidth (system.short j)) ≤ 3 * price := by
    calc
      _ ≤ ∑ _j : Fin 3, price := Finset.sum_le_sum (fun j _ => (rationalWordWidth_of_height (hSystem.2.2.1 j)).trans (model.word_le _))
      _ = _ := by simp
  have hInitial : (∑ j : Fin 3, rationalWordWidth (system.initial j)) ≤ 3 * price := by
    calc
      _ ≤ ∑ _j : Fin 3, price := Finset.sum_le_sum (fun j _ => (rationalWordWidth_of_height (hSystem.2.2.2 j)).trans (model.word_le _))
      _ = _ := by simp
  change i.reflectedResourcePayloadBitCost hcase ≤ 20 * price
  unfold reflectedResourcePayloadBitCost
  change 2 * (rationalWordWidth system.M + (∑ j, rationalWordWidth (system.long j)) +
    (∑ j, rationalWordWidth (system.short j)) + ∑ j, rationalWordWidth (system.initial j)) ≤ 20 * price
  omega

def reflectedResourcePreparationBitCost (model : RationalCostModel) (i : RationalFourInput)
    (hcase : i.w < (1 - i.p) * i.ell) : ℕ :=
  RationalFourParameterTable.preparationBitCost model i + RationalReflectedResourceCode.formulaBitCost model i +
    i.reflectedResourcePayloadBitCost hcase

theorem FieldsHeight.reflectedResourcePreparationBitCost_bound {i : RationalFourInput} {s : ℕ}
    (h : i.FieldsHeight s) (hs : 2 ≤ s) (hcase : i.w < (1 - i.p) * i.ell) (model : RationalCostModel) :
    i.reflectedResourcePreparationBitCost model hcase ≤ 2112 * model.rat (1 + 2 * expressionHeightBudget s 14) := by
  have hp := (RationalFourParameterTable.preparationBitCost_bound h hs model).trans (Nat.mul_le_mul_left 2068
    (model.monotone (Nat.add_le_add_left (Nat.mul_le_mul_left 2 (expressionHeightBudget_mono s (by decide : 12 ≤ 14))) 1)))
  have hf := RationalReflectedResourceCode.formulaBitCost_bound h hs model
  have hw := h.reflectedResourcePayloadBitCost_bound hs hcase model
  unfold reflectedResourcePreparationBitCost
  omega

end Blotto.RationalFourInput
