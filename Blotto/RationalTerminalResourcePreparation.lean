import Blotto.RationalNestedSpecPreparation
import Blotto.RationalPermutationPreparation

/-! Terminal compilation includes focus tests, endpoint tests, the actual
fractional weight and written nested-input fields. Dense output rows may reread
uncached child endpoint formulas three times, so three child-construction prices
are retained conservatively. Index/tag/backend/ownership work is separate. -/

namespace Blotto.RationalTerminalResourceCode

abbrev Expr := RationalExpression 3
def capacity : Expr := .sub (.input 0) (.input 1)
def weight : Expr := .div (.input 2) capacity
def environment (i : RationalTerminalResources) (j : Fin 3) : FixedArrayTable 3 ℚ :=
  FixedArrayTable.ofFn ![i.long j, i.short j, i.resource j]

theorem capacity_value (i : RationalTerminalResources) (j : Fin 3) :
    capacity.value (environment i j) = i.capacity j := by
  simp [capacity, environment, FixedArrayTable.read_ofFn, RationalTerminalResources.capacity]

theorem weight_value (i : RationalTerminalResources) (j : Fin 3) :
    weight.value (environment i j) = i.weight j := by
  simp [weight, capacity, environment, FixedArrayTable.read_ofFn,
    RationalTerminalResources.weight, RationalTerminalResources.capacity]

theorem environment_height {i : RationalTerminalResources} {s : ℕ} (h : i.FieldsHeight s) (j : Fin 3) :
    ∀ k, RationalHeight ((environment i j).read k) s := by
  intro k
  fin_cases k
  · simpa [environment, FixedArrayTable.read_ofFn] using h.2.1 j
  · simpa [environment, FixedArrayTable.read_ofFn] using h.2.2.1 j
  · simpa [environment, FixedArrayTable.read_ofFn] using h.2.2.2 j

def capacityBitCost (model : RationalCostModel) (i : RationalTerminalResources) (j : Fin 3) : ℕ :=
  capacity.bitCost model (environment i j) + rationalWordWidth (i.capacity j)

theorem capacityBitCost_bound {i : RationalTerminalResources} {s : ℕ} (h : i.FieldsHeight s)
    (model : RationalCostModel) (j : Fin 3) :
    capacityBitCost model i j ≤ 4 * model.rat (1 + 2 * expressionHeightBudget s 1) := by
  have hLit : capacity.LiteralHeights s := by simp [capacity, RationalExpression.LiteralHeights]
  have ha := capacity.run_all_heights _ s (environment_height h j) hLit
  have hd : capacity.depth = 1 := by decide
  rw [hd] at ha
  have hc := capacity.bitCost_bound model _ _ ha
  have ho : capacity.operationBound = 3 := by decide
  rw [ho] at hc
  have hv := capacity.run_height _ s (environment_height h j) hLit
  change RationalHeight (capacity.value (environment i j)) (expressionHeightBudget s capacity.depth) at hv
  rw [capacity_value, hd] at hv
  have hw := (rationalWordWidth_of_height hv).trans (model.word_le _)
  unfold capacityBitCost
  omega

def weightBitCost (model : RationalCostModel) (i : RationalTerminalResources) (j : Fin 3) : ℕ :=
  weight.bitCost model (environment i j) + rationalWordWidth (i.weight j)

theorem weightBitCost_bound {i : RationalTerminalResources} {s : ℕ} (h : i.FieldsHeight s)
    (model : RationalCostModel) (j : Fin 3) :
    weightBitCost model i j ≤ 7 * model.rat (1 + 2 * expressionHeightBudget s 2) := by
  have hLit : weight.LiteralHeights s := by simp [weight, capacity, RationalExpression.LiteralHeights]
  have ha := weight.run_all_heights _ s (environment_height h j) hLit
  have hd : weight.depth = 2 := by decide
  rw [hd] at ha
  have hc := weight.bitCost_bound model _ _ ha
  have ho : weight.operationBound = 6 := by decide
  rw [ho] at hc
  have hv := weight.run_height _ s (environment_height h j) hLit
  change RationalHeight (weight.value (environment i j)) (expressionHeightBudget s weight.depth) at hv
  rw [weight_value, hd] at hv
  have hw := (rationalWordWidth_of_height hv).trans (model.word_le _)
  unfold weightBitCost
  omega

end Blotto.RationalTerminalResourceCode
namespace Blotto.RationalTerminalResources
open scoped BigOperators

def focusBitCost (model : RationalCostModel) (i : RationalTerminalResources) : ℕ :=
  (RationalTerminalResourceCode.capacityBitCost model i 0 +
    RationalPreparationComparison.bitCost model 0 (i.resource 0) +
    RationalPreparationComparison.bitCost model (i.resource 0) (i.capacity 0)) +
  (RationalTerminalResourceCode.capacityBitCost model i 1 +
    RationalPreparationComparison.bitCost model 0 (i.resource 1) +
    RationalPreparationComparison.bitCost model (i.resource 1) (i.capacity 1))

theorem FieldsHeight.focusBitCost_bound {i : RationalTerminalResources} {s : ℕ} (h : i.FieldsHeight s)
    (hs : 2 ≤ s) (model : RationalCostModel) :
    i.focusBitCost model ≤ 20 * model.rat (1 + 2 * expressionHeightBudget s 1) := by
  have hZero : RationalHeight (0 : ℚ) (expressionHeightBudget s 1) :=
    (show RationalHeight (0 : ℚ) 2 by norm_num [RationalHeight]).mono (hs.trans (expressionHeightBudget_ge_input s 1))
  have hTerm : ∀ j : Fin 3,
      RationalTerminalResourceCode.capacityBitCost model i j + RationalPreparationComparison.bitCost model 0 (i.resource j) +
        RationalPreparationComparison.bitCost model (i.resource j) (i.capacity j) ≤ 10 * model.rat (1 + 2 * expressionHeightBudget s 1) := by
    intro j
    have hc := RationalTerminalResourceCode.capacityBitCost_bound h model j
    have hr := (h.2.2.2 j).mono (expressionHeightBudget_ge_input s 1)
    have hCap := (h.2.1 j).sub (h.2.2.1 j)
    change RationalHeight (i.capacity j) (s + s + 1) at hCap
    have he : s + s + 1 = expressionHeightBudget s 1 := by norm_num [expressionHeightBudget]; omega
    rw [he] at hCap
    have hA := RationalPreparationComparison.bitCost_bound model 0 (i.resource j) _ hZero hr
    have hB := RationalPreparationComparison.bitCost_bound model (i.resource j) (i.capacity j) _ hr hCap
    omega
  have h0 := hTerm 0
  have h1 := hTerm 1
  unfold focusBitCost
  omega

def inputDataBitCost (model : RationalCostModel) (i : RationalTerminalResources) : ℕ :=
  6 * i.focusBitCost model + RationalPreparationComparison.bitCost model (i.resource (i.permutation 0)) 0 +
    RationalPreparationComparison.bitCost model (i.resource (i.permutation 1)) 0 +
      RationalTerminalResourceCode.weightBitCost model i i.focus +
        2 * ∑ j : Fin 6, rationalWordWidth (RationalNestedSpec.sortedInputFields i.input j)

theorem FieldsHeight.inputDataBitCost_bound {i : RationalTerminalResources} {s : ℕ} (h : i.FieldsHeight s)
    (hs : 2 ≤ s) (model : RationalCostModel) :
    i.inputDataBitCost model ≤ 145 * model.rat (1 + 2 * expressionHeightBudget s 2) := by
  let price := model.rat (1 + 2 * expressionHeightBudget s 2)
  have hFocus := (h.focusBitCost_bound hs model).trans (Nat.mul_le_mul_left 20 (model.heightPrice_mono (le_refl s) (by decide : 1 ≤ 2)))
  have hm := expressionHeightBudget_ge_input s 2
  have hZero : RationalHeight (0 : ℚ) (expressionHeightBudget s 2) :=
    (show RationalHeight (0 : ℚ) 2 by norm_num [RationalHeight]).mono (hs.trans hm)
  have hA := RationalPreparationComparison.bitCost_bound model (i.resource (i.permutation 0)) 0 _ ((h.2.2.2 _).mono hm) hZero
  have hB := RationalPreparationComparison.bitCost_bound model (i.resource (i.permutation 1)) 0 _ ((h.2.2.2 _).mono hm) hZero
  have hWeight := RationalTerminalResourceCode.weightBitCost_bound h model i.focus
  have hInput := h.input
  have hFields : ∀ j, RationalHeight (RationalNestedSpec.sortedInputFields i.input j) (expressionHeightBudget s 2) := by
    intro j
    fin_cases j
    · exact hInput.1
    · exact hInput.2.1.min hInput.2.2.1
    · exact hInput.2.1.max hInput.2.2.1
    · exact hInput.2.2.2.1
    · exact hInput.2.2.2.2.1
    · exact hInput.2.2.2.2.2
  have hCopies : (∑ j : Fin 6, rationalWordWidth (RationalNestedSpec.sortedInputFields i.input j)) ≤ 6 * price := by
    calc
      _ ≤ ∑ _j : Fin 6, price := Finset.sum_le_sum (fun j _ => (rationalWordWidth_of_height (hFields j)).trans (model.word_le _))
      _ = _ := by simp
  unfold inputDataBitCost
  omega

noncomputable def profilePreparedBitCost (model : RationalCostModel) (primitive : ℕ → ℕ)
    (i : RationalTerminalResources) (K : ℕ) (outerBits : Fin K → Bool) : ℕ :=
  i.inputDataBitCost model + 3 * i.input.profilePreparedBitCost model primitive K outerBits +
    RationalPermutationCode.preparedDescriptorBitCost model (i.input.profile K outerBits) i.permutation

theorem FieldsHeight.profilePreparedBitCost_bound {i : RationalTerminalResources} {s : ℕ}
    (h : i.FieldsHeight s) (hs : 2 ≤ s) (model : RationalCostModel) (primitive : ℕ → ℕ)
    (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w) (K : ℕ) (outerBits : Fin K → Bool) :
    i.profilePreparedBitCost model primitive K outerBits ≤
      3 * RationalNestedInput.preparationNumericBitWork c K +
        26000 * model.rat (1 + 2 * expressionHeightBudget (max s (K + 2)) 47) := by
  let w := max s (K + 2)
  let price := model.rat (1 + 2 * expressionHeightBudget w 47)
  have hW := h.mono (le_max_left s (K + 2))
  have hw := hs.trans (le_max_left s (K + 2))
  have hData := (hW.inputDataBitCost_bound hw model).trans (Nat.mul_le_mul_left 145
    (model.heightPrice_mono (le_refl w) (by decide : 2 ≤ 47)))
  have hCore := hW.input.profilePreparedBitCost_bound (hw.trans (expressionHeightBudget_ge_input w 2))
    model primitive c hPrimitive K outerBits
  rw [max_eq_left ((le_max_right s (K + 2)).trans (expressionHeightBudget_ge_input w 2))] at hCore
  unfold RationalNestedInput.preparationWidth at hCore
  rw [expressionHeightBudget_comp] at hCore
  have hTable := hW.input.profile (hw.trans (expressionHeightBudget_ge_input w 2)) K outerBits
  rw [max_eq_left ((le_max_right s (K + 2)).trans (expressionHeightBudget_ge_input w 2)), expressionHeightBudget_comp] at hTable
  have hMap := RationalPermutationCode.preparedDescriptorBitCost_bound model (i.input.profile K outerBits) i.permutation _
    (hw.trans (expressionHeightBudget_ge_input w 47)) hTable
  change i.inputDataBitCost model ≤ 145 * price at hData
  change i.input.profilePreparedBitCost model primitive K outerBits ≤
    RationalNestedInput.preparationNumericBitWork c K + 8000 * price at hCore
  change RationalPermutationCode.preparedDescriptorBitCost model (i.input.profile K outerBits) i.permutation ≤ 1746 * price at hMap
  change i.profilePreparedBitCost model primitive K outerBits ≤ 3 * RationalNestedInput.preparationNumericBitWork c K + 26000 * price
  unfold profilePreparedBitCost
  omega

end Blotto.RationalTerminalResources
