import Blotto.RationalFirstConditionalPreparation
import Blotto.DyadicMidpointDecodeWork

/-! The actual finite outer block produces a location before constructing the
first conditional table. This prices one such factory invocation, keeping the
natural primitive envelope and all omitted metadata/backend costs explicit. -/

namespace Blotto.RationalNestedInput
open scoped BigOperators

def midpointLocationFormulaBitCost (model : RationalCostModel) (i : RationalNestedInput)
    (K : ℕ) (outerBits : Fin K → Bool) : ℕ :=
  let x := dyadicMidpointSample K outerBits
  (∑ j : Fin 7, rationalWordWidth ((RationalNestedParametersCode.environment i x).read j)) +
    (RationalNestedParametersCode.scalarPrograms 0).bitCost model (RationalNestedParametersCode.environment i x) +
      rationalWordWidth (i.midpointLocation K outerBits)

theorem FieldsHeight.midpointLocationFormulaBitCost_bound {i : RationalNestedInput} {s : ℕ}
    (h : i.FieldsHeight s) (hs : 2 ≤ s) (model : RationalCostModel) (K : ℕ) (outerBits : Fin K → Bool) :
    i.midpointLocationFormulaBitCost model K outerBits ≤
      136 * model.rat (1 + 2 * expressionHeightBudget (max s (K + 2)) 8) := by
  let w := max s (K + 2)
  let x := dyadicMidpointSample K outerBits
  let W := 1 + 2 * expressionHeightBudget w 8
  have hw : 2 ≤ w := hs.trans (le_max_left _ _)
  have hFields := h.mono (le_max_left s (K + 2))
  have hX := (dyadicMidpointSample_height K outerBits).mono (le_max_right s (K + 2))
  have hEnv := hFields.environment x hX
  have hCopies : (∑ j : Fin 7, rationalWordWidth ((RationalNestedParametersCode.environment i x).read j)) ≤ 7 * model.rat W := by
    calc
      _ ≤ ∑ _j : Fin 7, model.rat W := Finset.sum_le_sum (fun j _ =>
        (rationalWordWidth_of_height ((hEnv j).mono (expressionHeightBudget_ge_input w 8))).trans (model.word_le W))
      _ = _ := by simp
  have hc := RationalNestedParametersCode.scalar_bitCost model i x 0 w hw hEnv
  have ho := (rationalWordWidth_of_height (h.midpointLocation hs K outerBits)).trans (model.word_le W)
  change (RationalNestedParametersCode.scalarPrograms 0).bitCost model (RationalNestedParametersCode.environment i x) ≤
    128 * model.rat W at hc
  change i.midpointLocationFormulaBitCost model K outerBits ≤ 136 * model.rat W
  unfold midpointLocationFormulaBitCost
  change (∑ j : Fin 7, rationalWordWidth ((RationalNestedParametersCode.environment i x).read j)) +
    (RationalNestedParametersCode.scalarPrograms 0).bitCost model (RationalNestedParametersCode.environment i x) +
      rationalWordWidth (i.midpointLocation K outerBits) ≤ 136 * model.rat W
  omega

noncomputable def firstMidpointPreparedBitCost (model : RationalCostModel) (primitive : ℕ → ℕ)
    (i : RationalNestedInput) (htv : i.t ≤ i.v) (K : ℕ) (outerBits : Fin K → Bool) : ℕ :=
  dyadicMidpointDecodeBitWork model primitive K outerBits + i.midpointLocationFormulaBitCost model K outerBits +
    i.firstConditionalPreparedBitCost model htv (i.midpointLocation K outerBits) (i.midpointLocation_bounds K outerBits)

theorem FieldsHeight.firstMidpointPreparedBitCost_bound {i : RationalNestedInput} {s : ℕ}
    (h : i.FieldsHeight s) (hs : 2 ≤ s) (model : RationalCostModel) (primitive : ℕ → ℕ)
    (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w) (htv : i.t ≤ i.v) (K : ℕ) (outerBits : Fin K → Bool) :
    i.firstMidpointPreparedBitCost model primitive htv K outerBits ≤
      3 * K + (4 + 2 * c) * K * binaryWordWidth K + c * (K + 2) +
        11 * model.rat (1 + 2 * expressionHeightBudget (K + 2) 3) +
          136 * model.rat (1 + 2 * expressionHeightBudget (max s (K + 2)) 8) +
            3052 * model.rat (1 + 2 * expressionHeightBudget (max s (K + 2)) 28) := by
  let w := max s (K + 2)
  have hm : s ≤ expressionHeightBudget w 8 := (le_max_left _ _).trans (expressionHeightBudget_ge_input w 8)
  have hd := dyadicMidpointDecodeBitWork_bound model primitive c hPrimitive K outerBits
  have hl := h.midpointLocationFormulaBitCost_bound hs model K outerBits
  have hp := (h.mono hm).firstConditionalPreparedBitCost_bound (hs.trans hm) model htv
    (i.midpointLocation K outerBits) (i.midpointLocation_bounds K outerBits) (h.midpointLocation hs K outerBits)
  rw [expressionHeightBudget_comp] at hp
  change i.firstConditionalPreparedBitCost model htv (i.midpointLocation K outerBits) (i.midpointLocation_bounds K outerBits) ≤
    3052 * model.rat (1 + 2 * expressionHeightBudget (max s (K + 2)) 28) at hp
  unfold firstMidpointPreparedBitCost
  omega

end Blotto.RationalNestedInput
