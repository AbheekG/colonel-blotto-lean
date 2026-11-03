import Blotto.RationalFourCompleteDataCharge
import Blotto.RationalFourEntryPreparation
import Blotto.RationalFourProcessingLedger

/-! The actual ordered four-controller has one reached data/primitive
observer and one Boolean observer, preceded by machine/start preparation.
Conservative producer allowances stay explicit. Remaining metadata/backend/
ownership and the global compiler composition are separate. -/

namespace Blotto.RationalFourInput

noncomputable def fourCompleteDataBitWork (i : RationalFourInput) (model : RationalCostModel) (primitive : ℕ → ℕ)
    (copyResources : Bool) (K : ℕ) (outerBits scalarBits : Fin K → Bool)
    (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) : ℕ :=
  4 * i.fourLocalInitialDataBitCost model + (i.machine K outerBits scalarBits).cachedCallbackWork
    (i.fourCompleteDataCharge model primitive copyResources K outerBits scalarBits)
    N bits (.state (i.start K outerBits scalarBits)) pos hpos

theorem FieldsHeight.fourCompleteDataBitWork_bound {i : RationalFourInput} {s : ℕ}
    (h : i.FieldsHeight s) (hs : 2 ≤ s) (model : RationalCostModel) (primitive : ℕ → ℕ)
    (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w) (copyResources : Bool) (K : ℕ)
    (outerBits scalarBits : Fin K → Bool) (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) :
    i.fourCompleteDataBitWork model primitive copyResources K outerBits scalarBits N bits pos hpos ≤
      2268 * RationalNestedInput.preparationNumericBitWork c K + 17200000 * model.rat (completeDataWidth (max s (K + 2))) := by
  let w := max s (K + 2)
  let price := model.rat (completeDataWidth w)
  have hW := h.mono (le_max_left s (K + 2))
  have hw := hs.trans (le_max_left s (K + 2))
  have hPrecision := le_max_right s (K + 2)
  have hp := (i.machine K outerBits scalarBits).cachedCallbackWork_state_bound_under
    (i.fourCallbackInvariant w) (hW.fourCallback_closed hw K hPrecision outerBits scalarBits)
    (i.fourCompleteDataCharge model primitive copyResources K outerBits scalarBits)
    (28 * RationalNestedInput.preparationNumericBitWork c K + 210064 * price)
    (fun cursor hCursor => hW.fourCompleteDataCharge_bound hw model primitive c hPrimitive copyResources K hPrecision
      outerBits scalarBits cursor hCursor) N bits (i.start K outerBits scalarBits)
    (hW.fourCallback_start hw K outerBits scalarBits) pos hpos
  have hr : (i.machine K outerBits scalarBits).rank (i.start K outerBits scalarBits) + 1 ≤ 81 := by
    have hc := i.machine_rank K outerBits scalarBits
    omega
  have hCallbacks := hp.trans (Nat.mul_le_mul_left _ hr)
  have hInit : i.fourLocalInitialDataBitCost model ≤ 21 * price := by
    unfold fourLocalInitialDataBitCost
    split
    · exact Nat.zero_le _
    · rename_i hcase
      have hSystem := hW.reflectedResourceSystem hw (lt_of_not_ge hcase)
      have hc := hSystem.initialDataBitCost_bound (hw.trans (expressionHeightBudget_ge_input w 14)) model
      rw [expressionHeightBudget_comp] at hc
      exact hc.trans (Nat.mul_le_mul_left 21 (model.monotone (completeDataWidth_components w).2.2))
  change i.fourCompleteDataBitWork model primitive copyResources K outerBits scalarBits N bits pos hpos ≤
    2268 * RationalNestedInput.preparationNumericBitWork c K + 17200000 * price
  unfold fourCompleteDataBitWork
  nlinarith

noncomputable def orderedCompleteProcessingAllowance (i : RationalFourInput) (model : RationalCostModel)
    (primitive : ℕ → ℕ) (copyResources : Bool) (K : ℕ) (outerBits scalarBits : Fin K → Bool)
    (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) : ℕ :=
  i.entryPreparationAllowance model + i.fourCompleteDataBitWork model primitive copyResources K outerBits scalarBits N bits pos hpos +
    i.fourBooleanControlWork K outerBits scalarBits N bits pos hpos

theorem FieldsHeight.orderedCompleteProcessingAllowance_bound {i : RationalFourInput} {s : ℕ}
    (h : i.FieldsHeight s) (hs : 2 ≤ s) (model : RationalCostModel) (primitive : ℕ → ℕ)
    (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w) (copyResources : Bool) (K : ℕ)
    (outerBits scalarBits : Fin K → Bool) (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) :
    i.orderedCompleteProcessingAllowance model primitive copyResources K outerBits scalarBits N bits pos hpos ≤
      2268 * RationalNestedInput.preparationNumericBitWork c K + 17575000 * model.rat (completeDataWidth (max s (K + 2))) +
        320 * fourControlWordHeight (max s (K + 2)) +
          (24 * fourControlWordHeight (max s (K + 2)) + 28) * (162 + 2 * (N - pos)) := by
  let w := max s (K + 2)
  have hW := h.mono (le_max_left s (K + 2))
  have hw := hs.trans (le_max_left s (K + 2))
  have hEntry := (hW.entryPreparationAllowance_bound hw model).trans (Nat.mul_le_mul_left 375000
    (model.heightPrice_mono (le_refl w) (by decide : 39 ≤ 73)))
  have hData := h.fourCompleteDataBitWork_bound hs model primitive c hPrimitive copyResources K outerBits scalarBits N bits pos hpos
  have hControl := hW.fourBooleanControlWork_bound hw K (le_max_right s (K + 2)) outerBits scalarBits N bits pos hpos
  change i.entryPreparationAllowance model ≤ 375000 * model.rat (completeDataWidth w) at hEntry
  change i.entryPreparationAllowance model ≤ 375000 * model.rat (completeDataWidth (max s (K + 2))) at hEntry
  unfold orderedCompleteProcessingAllowance
  omega

end Blotto.RationalFourInput
