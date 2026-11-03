import Blotto.RationalSmallCompleteDataCharge
import Blotto.RationalSmallControlWork

/-! One small binary controller carries full reached data charges and its
actual Boolean-control observer. Four available-data allowances retain dense
producer rereads. Construction, later maps and metadata/backend remain separate. -/

namespace Blotto.RationalFourInput

noncomputable def smallCompleteDataBitWork (i : RationalFourInput) (hcase : i.w < (1 - i.p) * i.ell)
    (model : RationalCostModel) (primitive : ℕ → ℕ) (copyResources : Bool) (K : ℕ)
    (outerBits scalarBits : Fin K → Bool) (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) : ℕ :=
  let system := i.reflectedResourceSystem hcase
  4 * rationalInitialDataBitCost model system.capacity system.initial +
    (i.smallMachine hcase K outerBits scalarBits).cachedCallbackWork
      (i.smallCompleteDataCharge hcase model primitive copyResources K outerBits scalarBits)
      N bits (.state .start) pos hpos

theorem FieldsHeight.smallCompleteDataBitWork_bound {i : RationalFourInput} {s : ℕ}
    (h : i.FieldsHeight s) (hs : 2 ≤ s) (hcase : i.w < (1 - i.p) * i.ell) (model : RationalCostModel)
    (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w) (copyResources : Bool) (K : ℕ)
    (outerBits scalarBits : Fin K → Bool) (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) :
    i.smallCompleteDataBitWork hcase model primitive copyResources K outerBits scalarBits N bits pos hpos ≤
      588 * RationalNestedInput.preparationNumericBitWork c K + 4500000 * model.rat (completeDataWidth (max s (K + 2))) := by
  let w := max s (K + 2)
  let price := model.rat (completeDataWidth w)
  have hW := h.mono (le_max_left s (K + 2))
  have hw := hs.trans (le_max_left s (K + 2))
  have hPrecision := le_max_right s (K + 2)
  have hp := (i.smallMachine hcase K outerBits scalarBits).cachedCallbackWork_state_bound_under
    (i.smallCallbackInvariant hcase w) (hW.smallCallback_closed hw hcase K hPrecision outerBits scalarBits)
    (i.smallCompleteDataCharge hcase model primitive copyResources K outerBits scalarBits)
    (28 * RationalNestedInput.preparationNumericBitWork c K + 210064 * price)
    (fun cursor hCursor => hW.smallCompleteDataCharge_bound hw hcase model primitive c hPrimitive copyResources K hPrecision
      outerBits scalarBits cursor hCursor) N bits BinaryState.start trivial pos hpos
  have hr : (i.smallMachine hcase K outerBits scalarBits).rank BinaryState.start + 1 ≤ 21 := by
    have hc := i.smallMachine_rank hcase K outerBits scalarBits
    omega
  have hCallbacks := hp.trans (Nat.mul_le_mul_left _ hr)
  have hSystem := hW.reflectedResourceSystem hw hcase
  have hInit := hSystem.initialDataBitCost_bound (hw.trans (expressionHeightBudget_ge_input w 14)) model
  rw [expressionHeightBudget_comp] at hInit
  have hCopies := hInit.trans (Nat.mul_le_mul_left 21 (model.monotone (completeDataWidth_components w).2.2))
  change rationalInitialDataBitCost model (i.reflectedResourceSystem hcase).capacity
    (i.reflectedResourceSystem hcase).initial ≤ 21 * price at hCopies
  change i.smallCompleteDataBitWork hcase model primitive copyResources K outerBits scalarBits N bits pos hpos ≤
    588 * RationalNestedInput.preparationNumericBitWork c K + 4500000 * price
  unfold smallCompleteDataBitWork
  dsimp only
  nlinarith

noncomputable def smallCompleteProcessingAllowance (i : RationalFourInput) (hcase : i.w < (1 - i.p) * i.ell)
    (model : RationalCostModel) (primitive : ℕ → ℕ) (copyResources : Bool) (K : ℕ)
    (outerBits scalarBits : Fin K → Bool) (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) : ℕ :=
  i.smallCompleteDataBitWork hcase model primitive copyResources K outerBits scalarBits N bits pos hpos +
    i.smallBooleanControlWork hcase K outerBits scalarBits N bits pos hpos

theorem FieldsHeight.smallCompleteProcessingAllowance_bound {i : RationalFourInput} {s : ℕ}
    (h : i.FieldsHeight s) (hs : 2 ≤ s) (hcase : i.w < (1 - i.p) * i.ell) (model : RationalCostModel)
    (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w) (copyResources : Bool) (K : ℕ)
    (outerBits scalarBits : Fin K → Bool) (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) :
    i.smallCompleteProcessingAllowance hcase model primitive copyResources K outerBits scalarBits N bits pos hpos ≤
      588 * RationalNestedInput.preparationNumericBitWork c K + 4500000 * model.rat (completeDataWidth (max s (K + 2))) +
        80 * smallControlWordHeight (max s (K + 2)) +
          (24 * smallControlWordHeight (max s (K + 2)) + 28) * (42 + 2 * (N - pos)) := by
  have hd := h.smallCompleteDataBitWork_bound hs hcase model primitive c hPrimitive copyResources K outerBits scalarBits N bits pos hpos
  have hc := h.smallBooleanControlWork_precision_bound hs hcase K outerBits scalarBits N bits pos hpos
  unfold smallCompleteProcessingAllowance
  omega

end Blotto.RationalFourInput
