import Blotto.RationalFourProcessingLedger
import Blotto.RationalFourSpecHeight
import Blotto.CachedControlOutputMap

/-! Unsorted four-group inputs retain the same local processing prices under
the native output permutation. Sorting/emission/factory prices are separate. -/

namespace Blotto.RationalFourSpec

def processingWork (i : RationalFourSpec) (model : RationalCostModel) (copyResources : Bool) (K : ℕ)
    (outerBits scalarBits : Fin K → Bool) (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) : ℕ :=
  i.input.fourLocalInitialDataBitCost model +
    (i.machine K outerBits scalarBits).cachedCallbackWork (i.input.fourCallbackBitCharge model copyResources K outerBits)
      N bits (.state (i.input.start K outerBits scalarBits)) pos hpos +
    (i.machine K outerBits scalarBits).cachedControlWork (fun _ => true) (fun w => 4 * w) FixedWordCoin.bodyAllowance
      N bits (.state (i.input.start K outerBits scalarBits)) pos hpos

theorem processingWork_refines (i : RationalFourSpec) (model : RationalCostModel) (copyResources : Bool) (K : ℕ)
    (outerBits scalarBits : Fin K → Bool) (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) :
    i.processingWork model copyResources K outerBits scalarBits N bits pos hpos =
      i.input.fourProcessingWork model copyResources K outerBits scalarBits N bits pos hpos := by
  unfold processingWork machine
  rw [WordStateMachine.cachedCallbackWork_mapped, WordStateMachine.cachedControlWork_mapped]
  rfl

theorem FieldsHeight.processingWork_bound {i : RationalFourSpec} {s : ℕ} (h : i.FieldsHeight s) (hs : 2 ≤ s)
    (model : RationalCostModel) (copyResources : Bool) (K : ℕ) (outerBits scalarBits : Fin K → Bool)
    (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) :
    i.processingWork model copyResources K outerBits scalarBits N bits pos hpos ≤
      53400 * model.rat (RationalFourInput.fourCallbackWidth (max s (K + 2))) +
        320 * RationalFourInput.fourControlWordHeight (max s (K + 2)) +
        (24 * RationalFourInput.fourControlWordHeight (max s (K + 2)) + 28) * (162 + 2 * (N - pos)) := by
  rw [processingWork_refines]
  exact h.input.fourProcessingWork_bound hs model copyResources K outerBits scalarBits N bits pos hpos

end Blotto.RationalFourSpec
namespace Blotto.RationalMixedGroupSpec

theorem fourProcessingWork_bound (i : RationalMixedGroupSpec 3) (s : ℕ) (hs : 2 ≤ s) (h : i.FieldsHeight s)
    (model : RationalCostModel) (copyResources : Bool) (K : ℕ) (outerBits scalarBits : Fin K → Bool)
    (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) :
    i.fourInput.processingWork model copyResources K outerBits scalarBits N bits pos hpos ≤
      53400 * model.rat (RationalFourInput.fourCallbackWidth (max s (K + 2))) +
        320 * RationalFourInput.fourControlWordHeight (max s (K + 2)) +
        (24 * RationalFourInput.fourControlWordHeight (max s (K + 2)) + 28) * (162 + 2 * (N - pos)) :=
  h.fourInput.processingWork_bound hs model copyResources K outerBits scalarBits N bits pos hpos

end Blotto.RationalMixedGroupSpec
