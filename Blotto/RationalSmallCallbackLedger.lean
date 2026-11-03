import Blotto.RationalSmallCallbackInvariant

/-! One small-case callback ledger covers root canonical fields, the uniform
categorical branch, or reflected resource/terminal callbacks. Local resource
initialization is charged before the root, since both start values are prepared.
Factories, available-field derivations, Boolean control/emission/backend remain separate. -/

namespace Blotto.RationalFourInput

def smallCallbackBitWork (i : RationalFourInput) (hcase : i.w < (1 - i.p) * i.ell)
    (model : RationalCostModel) (copyResources : Bool) (K : ℕ) (outerBits scalarBits : Fin K → Bool)
    (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) : ℕ :=
  (i.smallMachine hcase K outerBits scalarBits).cachedCallbackWork
    (i.smallCallbackBitCharge hcase model copyResources K outerBits) N bits (.state .start) pos hpos

theorem FieldsHeight.smallCallbackBitWork_bound {i : RationalFourInput} {s : ℕ} (h : i.FieldsHeight s) (hs : 2 ≤ s)
    (hcase : i.w < (1 - i.p) * i.ell) (model : RationalCostModel) (copyResources : Bool) (K : ℕ)
    (hPrecision : K + 2 ≤ s) (outerBits scalarBits : Fin K → Bool)
    (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) :
    i.smallCallbackBitWork hcase model copyResources K outerBits scalarBits N bits pos hpos ≤
      (if copyResources then 6279 else 6195) * model.rat (smallCallbackWidth s) := by
  have hp := (i.smallMachine hcase K outerBits scalarBits).cachedCallbackWork_state_bound_under
    (i.smallCallbackInvariant hcase s) (h.smallCallback_closed hs hcase K hPrecision outerBits scalarBits)
    (i.smallCallbackBitCharge hcase model copyResources K outerBits)
    ((if copyResources then 299 else 295) * model.rat (smallCallbackWidth s))
    (h.smallCallbackBitCharge_bound hs hcase model copyResources K hPrecision outerBits)
    N bits .start (h.smallCallback_start hcase) pos hpos
  have hr := i.smallMachine_rank hcase K outerBits scalarBits
  have hc : (i.smallMachine hcase K outerBits scalarBits).rank .start + 1 ≤ 21 := by omega
  have hTotal := hp.trans (Nat.mul_le_mul_left _ hc)
  change i.smallCallbackBitWork hcase model copyResources K outerBits scalarBits N bits pos hpos ≤
    ((if copyResources then 299 else 295) * model.rat (smallCallbackWidth s)) * 21 at hTotal
  have hPrice : ((if copyResources then 299 else 295) * model.rat (smallCallbackWidth s)) * 21 =
      (if copyResources then 6279 else 6195) * model.rat (smallCallbackWidth s) := by
    cases copyResources <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> ring
  exact hTotal.trans_eq hPrice

def smallDataAndCallbackBitWork (i : RationalFourInput) (hcase : i.w < (1 - i.p) * i.ell)
    (model : RationalCostModel) (copyResources : Bool) (K : ℕ) (outerBits scalarBits : Fin K → Bool)
    (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) : ℕ :=
  rationalInitialDataBitCost model (i.reflectedResourceSystem hcase).capacity (i.reflectedResourceSystem hcase).initial +
    i.smallCallbackBitWork hcase model copyResources K outerBits scalarBits N bits pos hpos

theorem FieldsHeight.smallDataAndCallbackBitWork_bound {i : RationalFourInput} {s : ℕ} (h : i.FieldsHeight s) (hs : 2 ≤ s)
    (hcase : i.w < (1 - i.p) * i.ell) (model : RationalCostModel) (copyResources : Bool) (K : ℕ)
    (hPrecision : K + 2 ≤ s) (outerBits scalarBits : Fin K → Bool)
    (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) :
    i.smallDataAndCallbackBitWork hcase model copyResources K outerBits scalarBits N bits pos hpos ≤
      (if copyResources then 6300 else 6216) * model.rat (smallCallbackWidth s) := by
  have hSystem := h.reflectedResourceSystem hs hcase
  have hInit := hSystem.initialDataBitCost_bound (hs.trans (expressionHeightBudget_ge_input s 14)) model
  rw [expressionHeightBudget_comp] at hInit
  have hData := hInit.trans (Nat.mul_le_mul_left 21 (model.monotone (smallCallback_widths s).2.2))
  have hCallbacks := h.smallCallbackBitWork_bound hs hcase model copyResources K hPrecision outerBits scalarBits N bits pos hpos
  unfold smallDataAndCallbackBitWork
  cases copyResources <;> simp only [Bool.false_eq_true, ite_false, ite_true] at hCallbacks ⊢ <;> omega

theorem FieldsHeight.smallDataAndCallbackBitWork_precision_bound {i : RationalFourInput} {s : ℕ} (h : i.FieldsHeight s) (hs : 2 ≤ s)
    (hcase : i.w < (1 - i.p) * i.ell) (model : RationalCostModel) (copyResources : Bool) (K : ℕ)
    (outerBits scalarBits : Fin K → Bool) (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) :
    i.smallDataAndCallbackBitWork hcase model copyResources K outerBits scalarBits N bits pos hpos ≤
      (if copyResources then 6300 else 6216) * model.rat (smallCallbackWidth (max s (K + 2))) :=
  (h.mono (le_max_left s (K + 2))).smallDataAndCallbackBitWork_bound (hs.trans (le_max_left s (K + 2)))
    hcase model copyResources K (le_max_right s (K + 2)) outerBits scalarBits N bits pos hpos

end Blotto.RationalFourInput
