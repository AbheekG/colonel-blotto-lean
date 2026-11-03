import Blotto.RationalFourCallbackInvariant

/-! Either selected four-variable regime has one indexed callback/control
ledger. Local resource initialization is included in the small regime.
Available-field derivations, descriptor/list factories, emission/address and
physical backend/ownership remain separate obligations. -/

namespace Blotto.RationalFourInput

def fourLocalInitialDataBitCost (i : RationalFourInput) (model : RationalCostModel) : ℕ :=
  if hcase : (1 - i.p) * i.ell ≤ i.w then 0
  else rationalInitialDataBitCost model (i.reflectedResourceSystem (lt_of_not_ge hcase)).capacity
    (i.reflectedResourceSystem (lt_of_not_ge hcase)).initial

def fourCallbackBitWork (i : RationalFourInput) (model : RationalCostModel) (copyResources : Bool) (K : ℕ)
    (outerBits scalarBits : Fin K → Bool) (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) : ℕ :=
  (i.machine K outerBits scalarBits).cachedCallbackWork (i.fourCallbackBitCharge model copyResources K outerBits)
    N bits (.state (i.start K outerBits scalarBits)) pos hpos

def fourBooleanControlWork (i : RationalFourInput) (K : ℕ) (outerBits scalarBits : Fin K → Bool)
    (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) : ℕ :=
  (i.machine K outerBits scalarBits).cachedControlWork (fun _ => true) (fun w => 4 * w) FixedWordCoin.bodyAllowance
    N bits (.state (i.start K outerBits scalarBits)) pos hpos

theorem FieldsHeight.fourLocalInitialDataBitCost_bound {i : RationalFourInput} {s : ℕ} (h : i.FieldsHeight s) (hs : 2 ≤ s)
    (model : RationalCostModel) : i.fourLocalInitialDataBitCost model ≤ 21 * model.rat (fourCallbackWidth s) := by
  unfold fourLocalInitialDataBitCost
  split_ifs with hcase
  · exact Nat.zero_le _
  · have hSystem := h.reflectedResourceSystem hs (lt_of_not_ge hcase)
    have hp := hSystem.initialDataBitCost_bound (hs.trans (expressionHeightBudget_ge_input s 14)) model
    rw [expressionHeightBudget_comp] at hp
    have hWidth : 1 + 2 * expressionHeightBudget s 15 ≤ fourCallbackWidth s :=
      (smallCallback_widths s).2.2.trans (fourCallback_widths s).2.1
    exact hp.trans (Nat.mul_le_mul_left 21 (model.monotone hWidth))

theorem FieldsHeight.fourCallbackBitWork_bound {i : RationalFourInput} {s : ℕ} (h : i.FieldsHeight s) (hs : 2 ≤ s)
    (model : RationalCostModel) (copyResources : Bool) (K : ℕ) (hPrecision : K + 2 ≤ s)
    (outerBits scalarBits : Fin K → Bool) (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) :
    i.fourCallbackBitWork model copyResources K outerBits scalarBits N bits pos hpos ≤ 53379 * model.rat (fourCallbackWidth s) := by
  have hp := (i.machine K outerBits scalarBits).cachedCallbackWork_state_bound_under
    (i.fourCallbackInvariant s) (h.fourCallback_closed hs K hPrecision outerBits scalarBits)
    (i.fourCallbackBitCharge model copyResources K outerBits) (659 * model.rat (fourCallbackWidth s))
    (h.fourCallbackBitCharge_bound hs model copyResources K hPrecision outerBits)
    N bits (i.start K outerBits scalarBits) (h.fourCallback_start hs K outerBits scalarBits) pos hpos
  have hr : (i.machine K outerBits scalarBits).rank (i.start K outerBits scalarBits) + 1 ≤ 81 := by
    have hc := i.machine_rank K outerBits scalarBits
    omega
  have hTotal := hp.trans (Nat.mul_le_mul_left _ hr)
  change i.fourCallbackBitWork model copyResources K outerBits scalarBits N bits pos hpos ≤
    (659 * model.rat (fourCallbackWidth s)) * 81 at hTotal
  have hPrice : (659 * model.rat (fourCallbackWidth s)) * 81 = 53379 * model.rat (fourCallbackWidth s) := by ring
  exact hTotal.trans_eq hPrice

theorem FieldsHeight.fourBooleanControlWork_bound {i : RationalFourInput} {s : ℕ} (h : i.FieldsHeight s) (hs : 2 ≤ s)
    (K : ℕ) (hPrecision : K + 2 ≤ s) (outerBits scalarBits : Fin K → Bool)
    (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) :
    i.fourBooleanControlWork K outerBits scalarBits N bits pos hpos ≤
      320 * fourControlWordHeight s + (24 * fourControlWordHeight s + 28) * (162 + 2 * (N - pos)) := by
  have hp := (i.machine K outerBits scalarBits).cachedControlWork_state_bound_under
    (i.fourCallbackInvariant s) (fourControlWordHeight s)
    (h.fourCallback_wordsHeight hs K hPrecision outerBits scalarBits)
    (h.fourCallback_closed hs K hPrecision outerBits scalarBits)
    N bits (i.start K outerBits scalarBits) (h.fourCallback_start hs K outerBits scalarBits)
    80 (i.machine_rank K outerBits scalarBits) pos hpos
  change i.fourBooleanControlWork K outerBits scalarBits N bits pos hpos ≤ _ at hp
  convert hp using 1; ring

def fourProcessingWork (i : RationalFourInput) (model : RationalCostModel) (copyResources : Bool) (K : ℕ)
    (outerBits scalarBits : Fin K → Bool) (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) : ℕ :=
  i.fourLocalInitialDataBitCost model + i.fourCallbackBitWork model copyResources K outerBits scalarBits N bits pos hpos +
    i.fourBooleanControlWork K outerBits scalarBits N bits pos hpos

theorem FieldsHeight.fourProcessingWork_bound {i : RationalFourInput} {s : ℕ} (h : i.FieldsHeight s) (hs : 2 ≤ s)
    (model : RationalCostModel) (copyResources : Bool) (K : ℕ) (outerBits scalarBits : Fin K → Bool)
    (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) :
    i.fourProcessingWork model copyResources K outerBits scalarBits N bits pos hpos ≤
      53400 * model.rat (fourCallbackWidth (max s (K + 2))) +
        320 * fourControlWordHeight (max s (K + 2)) +
        (24 * fourControlWordHeight (max s (K + 2)) + 28) * (162 + 2 * (N - pos)) := by
  have hWide := h.mono (le_max_left s (K + 2))
  have hsWide := hs.trans (le_max_left s (K + 2))
  have hInit := hWide.fourLocalInitialDataBitCost_bound hsWide model
  have hCallbacks := hWide.fourCallbackBitWork_bound hsWide model copyResources K (le_max_right s (K + 2))
    outerBits scalarBits N bits pos hpos
  have hControl := hWide.fourBooleanControlWork_bound hsWide K (le_max_right s (K + 2))
    outerBits scalarBits N bits pos hpos
  unfold fourProcessingWork
  nlinarith

end Blotto.RationalFourInput
