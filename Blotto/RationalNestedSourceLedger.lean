import Blotto.RationalNestedStoreWork

/-! One local packet carries initialization, shared pair requests, selected
stores and retention tests. This combines actual operand/copy prices; available
field derivations, factories, Boolean control/output/backend remain separate. -/

namespace Blotto.RationalNestedResourceSystem

theorem FieldsHeight.initialDataBitCost_bound {i : RationalNestedResourceSystem} {s : ℕ} (h : i.FieldsHeight s)
    (hs : 2 ≤ s) (model : RationalCostModel) :
    rationalInitialDataBitCost model i.capacity i.initial ≤ 21 * model.rat (1 + 2 * expressionHeightBudget s 1) := by
  apply rationalInitialDataBitCost_bound model i.capacity i.initial
  · have hz : rationalWordWidth (0 : ℚ) = 3 := by decide
    have hm := expressionHeightBudget_ge_input s 1
    omega
  · intro j
    exact rationalWordWidth_of_height (h.capacity j)
  · intro j
    exact rationalWordWidth_of_height ((h.2.2.2 j).mono (expressionHeightBudget_ge_input s 1))

def localSourceDataBitWork (i : RationalNestedResourceSystem) (model : RationalCostModel) (copyResources : Bool) (K : ℕ)
    (outerBits scalarBits : Fin K → Bool) (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) : ℕ :=
  rationalInitialDataBitCost model i.capacity i.initial + i.phaseRequestBitWork model K outerBits scalarBits N bits pos hpos +
    i.phaseStoreBitWork model copyResources K outerBits scalarBits N bits pos hpos +
    i.phaseRetainedBitWork model K outerBits scalarBits N bits pos hpos

theorem FieldsHeight.localSourceDataBitWork_bound {i : RationalNestedResourceSystem} {s : ℕ} (h : i.FieldsHeight s)
    (hs : 2 ≤ s) (model : RationalCostModel) (copyResources : Bool) (K : ℕ) (outerBits scalarBits : Fin K → Bool)
    (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) :
    i.localSourceDataBitWork model copyResources K outerBits scalarBits N bits pos hpos ≤
      (if copyResources then 407 else 399) * model.rat (32 * expressionHeightBudget s 7 + 31) := by
  let W := 32 * expressionHeightBudget s 7 + 31
  have hm := expressionHeightBudget_mono s (by decide : 1 ≤ 7)
  have hInitWidth : 1 + 2 * expressionHeightBudget s 1 ≤ W := by dsimp [W]; omega
  have hStoreWidth : 8 * expressionHeightBudget s 7 + 7 ≤ W := by dsimp [W]; omega
  have hRetWidth : 1 + 2 * expressionHeightBudget s 7 ≤ W := by dsimp [W]; omega
  have hInit := (h.initialDataBitCost_bound hs model).trans (Nat.mul_le_mul_left 21 (model.monotone hInitWidth))
  have hRequest := h.phaseRequestBitWork_bound hs model K outerBits scalarBits N bits pos hpos
  change i.phaseRequestBitWork model K outerBits scalarBits N bits pos hpos ≤ 294 * model.rat W at hRequest
  have hStore := (h.phaseStoreBitWork_bound hs model copyResources K outerBits scalarBits N bits pos hpos).trans
    (Nat.mul_le_mul_left (if copyResources then 72 else 64) (model.monotone hStoreWidth))
  have hRet := (h.phaseRetainedBitWork_bound hs model K outerBits scalarBits N bits pos hpos).trans
    (Nat.mul_le_mul_left 20 (model.monotone hRetWidth))
  change i.localSourceDataBitWork model copyResources K outerBits scalarBits N bits pos hpos ≤
    (if copyResources then 407 else 399) * model.rat W
  unfold localSourceDataBitWork
  cases copyResources <;> simp only [Bool.false_eq_true, ite_false, ite_true] at hStore ⊢ <;> omega

def localSourceAndTerminalBitWork (i : RationalNestedResourceSystem) (model : RationalCostModel) (copyResources : Bool) (K : ℕ)
    (outerBits scalarBits : Fin K → Bool) (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) : ℕ :=
  i.localSourceDataBitWork model copyResources K outerBits scalarBits N bits pos hpos +
    i.terminalCategoricalBitWork model K outerBits scalarBits N bits pos hpos

theorem FieldsHeight.localSourceAndTerminalBitWork_bound {i : RationalNestedResourceSystem} {s : ℕ} (h : i.FieldsHeight s)
    (hs : 2 ≤ s) (model : RationalCostModel) (copyResources : Bool) (K : ℕ) (hPrecision : K + 2 ≤ s)
    (outerBits scalarBits : Fin K → Bool) (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) :
    i.localSourceAndTerminalBitWork model copyResources K outerBits scalarBits N bits pos hpos ≤
      (if copyResources then 407 else 399) * model.rat (32 * expressionHeightBudget s 7 + 31) +
        2790 * model.rat (categoricalRequestWidth 18 (expressionHeightBudget s 54)) :=
  Nat.add_le_add (h.localSourceDataBitWork_bound hs model copyResources K outerBits scalarBits N bits pos hpos)
    (h.terminalCategoricalBitWork_bound hs model K hPrecision outerBits scalarBits N bits pos hpos)

end Blotto.RationalNestedResourceSystem
