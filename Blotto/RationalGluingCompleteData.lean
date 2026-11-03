import Blotto.RationalSmallCompleteDataCharge
import Blotto.RationalSegmentDecodedEmission

/-! The actual gluing categorical and decoded-interpolation callback prices
join at the same indexed reader. All 81 slots remain covered. Construction,
Boolean control, later maps and metadata/backend are separate. -/

namespace Blotto.RationalFourInput

theorem gluingCompleteDataWidth (s : ℕ) :
    categoricalRequestWidth 81 (expressionHeightBudget s 36) ≤ completeDataWidth s := by
  have h43 : expressionHeightBudget s 43 = 128 * expressionHeightBudget s 36 + 127 := by
    rw [show 43 = 36 + 7 by decide, ← expressionHeightBudget_comp]
    change (expressionHeightBudget s 36 + 1) * 128 - 1 = _
    omega
  have hm := expressionHeightBudget_mono s (by decide : 43 ≤ 73)
  unfold categoricalRequestWidth completeDataWidth
  omega

def gluingCompleteDataBitWork (i : RationalFourInput) (hcase : (1 - i.p) * i.ell ≤ i.w)
    (model : RationalCostModel) (primitive : ℕ → ℕ) (K : ℕ) (scalarBits : Fin K → Bool)
    (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) : ℕ :=
  (i.gluingDescriptor hcase).dataAndCallbackBitWork model primitive 0 K scalarBits N bits pos hpos

theorem FieldsHeight.gluingCompleteDataBitWork_bound {i : RationalFourInput} {s : ℕ}
    (h : i.FieldsHeight s) (hs : 2 ≤ s) (hcase : (1 - i.p) * i.ell ≤ i.w)
    (model : RationalCostModel) (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w) (K : ℕ)
    (scalarBits : Fin K → Bool) (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) :
    i.gluingCompleteDataBitWork hcase model primitive K scalarBits N bits pos hpos ≤
      RationalNestedInput.preparationNumericBitWork c K + 53442 * model.rat (completeDataWidth (max s (K + 2))) := by
  let w := max s (K + 2)
  let price := model.rat (completeDataWidth w)
  have hw := hs.trans (le_max_left s (K + 2))
  have hp := ((h.mono (le_max_left s (K + 2))).gluingDescriptor hw hcase).dataAndCallbackBitWork_bound
    (hw.trans (expressionHeightBudget_ge_input w 36)) model primitive c hPrimitive 0 K scalarBits N bits pos hpos
  rw [max_eq_left ((le_max_right s (K + 2)).trans (expressionHeightBudget_ge_input w 36)), expressionHeightBudget_comp] at hp
  have hCat : model.rat (categoricalRequestWidth 81 (expressionHeightBudget w 36)) ≤ price := model.monotone (gluingCompleteDataWidth w)
  have hMid : model.rat (1 + 2 * expressionHeightBudget (K + 2) 3) ≤ price := model.heightPrice_mono (le_max_right s (K + 2)) (by decide : 3 ≤ 73)
  have hPoint : model.rat (1 + 2 * expressionHeightBudget w 39) ≤ price := model.heightPrice_mono (le_refl w) (by decide : 39 ≤ 73)
  change i.gluingCompleteDataBitWork hcase model primitive K scalarBits N bits pos hpos ≤
    53379 * model.rat (categoricalRequestWidth 81 (expressionHeightBudget w 36)) +
      (RationalNestedInput.preparationNumericBitWork c K + 11 * model.rat (1 + 2 * expressionHeightBudget (K + 2) 3) +
        52 * model.rat (1 + 2 * expressionHeightBudget w 39)) at hp
  change i.gluingCompleteDataBitWork hcase model primitive K scalarBits N bits pos hpos ≤
    RationalNestedInput.preparationNumericBitWork c K + 53442 * price
  omega

end Blotto.RationalFourInput
