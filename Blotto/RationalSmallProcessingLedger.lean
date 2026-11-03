import Blotto.RationalSmallControlWork

/-! The same indexed small-case path carries available-data/callback prices
and Boolean encoding/coin-body allowances. The declared bit backend, available
field derivations, factories, emission/address/allocator/ownership are separate. -/

namespace Blotto.RationalFourInput

def smallProcessingWork (i : RationalFourInput) (hcase : i.w < (1 - i.p) * i.ell)
    (model : RationalCostModel) (copyResources : Bool) (K : ℕ) (outerBits scalarBits : Fin K → Bool)
    (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) : ℕ :=
  i.smallDataAndCallbackBitWork hcase model copyResources K outerBits scalarBits N bits pos hpos +
    i.smallBooleanControlWork hcase K outerBits scalarBits N bits pos hpos

theorem FieldsHeight.smallProcessingWork_bound {i : RationalFourInput} {s : ℕ} (h : i.FieldsHeight s) (hs : 2 ≤ s)
    (hcase : i.w < (1 - i.p) * i.ell) (model : RationalCostModel) (copyResources : Bool) (K : ℕ)
    (outerBits scalarBits : Fin K → Bool) (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) :
    i.smallProcessingWork hcase model copyResources K outerBits scalarBits N bits pos hpos ≤
      (if copyResources then 6300 else 6216) * model.rat (smallCallbackWidth (max s (K + 2))) +
        80 * smallControlWordHeight (max s (K + 2)) +
        (24 * smallControlWordHeight (max s (K + 2)) + 28) * (42 + 2 * (N - pos)) := by
  have hData := h.smallDataAndCallbackBitWork_precision_bound hs hcase model copyResources K outerBits scalarBits N bits pos hpos
  have hControl := h.smallBooleanControlWork_precision_bound hs hcase K outerBits scalarBits N bits pos hpos
  have hp := Nat.add_le_add hData hControl
  simpa only [smallProcessingWork, Nat.add_assoc] using hp

end Blotto.RationalFourInput
