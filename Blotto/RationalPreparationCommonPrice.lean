import Blotto.RationalSecondUniformPreparation
import Blotto.RationalNestedFamilyPreparation

/-! Common word envelopes combine nested construction components. The natural
primitive envelope remains explicit; these do not certify physical execution. -/

namespace Blotto

theorem expressionHeightBudget_input_mono {s t : ℕ} (h : s ≤ t) (d : ℕ) :
    expressionHeightBudget s d ≤ expressionHeightBudget t d := by
  unfold expressionHeightBudget
  exact Nat.sub_le_sub_right (Nat.mul_le_mul_right _ (Nat.add_le_add_right h 1)) 1

theorem RationalCostModel.heightPrice_mono (model : RationalCostModel) {s t a b : ℕ}
    (hst : s ≤ t) (hab : a ≤ b) :
    model.rat (1 + 2 * expressionHeightBudget s a) ≤ model.rat (1 + 2 * expressionHeightBudget t b) :=
  model.monotone (Nat.add_le_add_left (Nat.mul_le_mul_left 2
    ((expressionHeightBudget_input_mono hst a).trans (expressionHeightBudget_mono t hab))) 1)

end Blotto
namespace Blotto.RationalNestedInput

def preparationNumericBitWork (c K : ℕ) : ℕ :=
  3 * K + (4 + 2 * c) * K * binaryWordWidth K + c * (K + 2)

def preparationWidth (s : ℕ) : ℕ := 1 + 2 * expressionHeightBudget s 45

theorem FieldsHeight.familyMidpointPreparedBitCost_common {i : RationalNestedInput} {s : ℕ}
    (h : i.FieldsHeight s) (hs : 2 ≤ s) (model : RationalCostModel) (primitive : ℕ → ℕ)
    (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w) (x : ℚ) (hx0 : 0 < x) (hxv : x ≤ i.v)
    (hX : RationalHeight x (expressionHeightBudget s 8)) (K : ℕ) (hK : K + 2 ≤ s) (outerBits : Fin K → Bool) :
    i.familyMidpointPreparedBitCost model primitive x hx0 hxv K outerBits ≤
      preparationNumericBitWork c K + 3333 * model.rat (preparationWidth s) := by
  let price := model.rat (preparationWidth s)
  have hm := expressionHeightBudget_ge_input s 8
  have hPrecision : K + 2 ≤ expressionHeightBudget s 16 := hK.trans (expressionHeightBudget_ge_input s 16)
  have hp := (h.mono hm).familyMidpointPreparedBitCost_bound (hs.trans hm) model primitive c hPrimitive
    x hx0 hxv hX K outerBits
  simp only [expressionHeightBudget_comp, max_eq_left hPrecision] at hp
  change i.familyMidpointPreparedBitCost model primitive x hx0 hxv K outerBits ≤
    134 * model.rat (1 + 2 * expressionHeightBudget s 16) +
      (preparationNumericBitWork c K + 11 * model.rat (1 + 2 * expressionHeightBudget (K + 2) 3) +
        136 * model.rat (1 + 2 * expressionHeightBudget s 24) +
          3052 * model.rat (1 + 2 * expressionHeightBudget s 44)) at hp
  have h16 : model.rat (1 + 2 * expressionHeightBudget s 16) ≤ price := model.heightPrice_mono (le_refl s) (by decide)
  have h24 : model.rat (1 + 2 * expressionHeightBudget s 24) ≤ price := model.heightPrice_mono (le_refl s) (by decide)
  have h44 : model.rat (1 + 2 * expressionHeightBudget s 44) ≤ price := model.heightPrice_mono (le_refl s) (by decide)
  have hk : model.rat (1 + 2 * expressionHeightBudget (K + 2) 3) ≤ price := model.heightPrice_mono hK (by decide)
  change i.familyMidpointPreparedBitCost model primitive x hx0 hxv K outerBits ≤ preparationNumericBitWork c K + 3333 * price
  omega

theorem FieldsHeight.firstMidpointPreparedBitCost_common {i : RationalNestedInput} {s : ℕ}
    (h : i.FieldsHeight s) (hs : 2 ≤ s) (model : RationalCostModel) (primitive : ℕ → ℕ)
    (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w) (htv : i.t ≤ i.v)
    (K : ℕ) (hK : K + 2 ≤ s) (outerBits : Fin K → Bool) :
    i.firstMidpointPreparedBitCost model primitive htv K outerBits ≤
      preparationNumericBitWork c K + 3199 * model.rat (preparationWidth s) := by
  let price := model.rat (preparationWidth s)
  have hp := h.firstMidpointPreparedBitCost_bound hs model primitive c hPrimitive htv K outerBits
  rw [max_eq_left hK] at hp
  have h8 : model.rat (1 + 2 * expressionHeightBudget s 8) ≤ price := model.heightPrice_mono (le_refl s) (by decide)
  have h28 : model.rat (1 + 2 * expressionHeightBudget s 28) ≤ price := model.heightPrice_mono (le_refl s) (by decide)
  have hk : model.rat (1 + 2 * expressionHeightBudget (K + 2) 3) ≤ price := model.heightPrice_mono hK (by decide)
  change i.firstMidpointPreparedBitCost model primitive htv K outerBits ≤ preparationNumericBitWork c K + 3199 * price
  unfold preparationNumericBitWork
  omega

end Blotto.RationalNestedInput
