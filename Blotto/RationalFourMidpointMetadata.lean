import Blotto.RationalLocalMidpointCharge
import Blotto.RationalFourSpecCompleteProcessing
import Blotto.CachedCallbackBounds

/-! Midpoint metadata accumulates on the actual ordered four-controller.
The unsorted dense wrapper retains the same four producer allowances as its
data ledger. The existing cap/position and all exhaustion branches are kept. -/

namespace Blotto.RationalFourInput

def fourMidpointMetadataBitWork (i : RationalFourInput) (primitive : ℕ → ℕ) (K : ℕ)
    (outerBits scalarBits : Fin K → Bool) (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) : ℕ :=
  (i.machine K outerBits scalarBits).cachedCallbackWork (i.fourMidpointMetadataCharge primitive K outerBits scalarBits)
    N bits (.state (i.start K outerBits scalarBits)) pos hpos

theorem fourMidpointMetadataBitWork_bound (i : RationalFourInput) (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c * w) (K : ℕ) (outerBits scalarBits : Fin K → Bool)
    (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) :
    i.fourMidpointMetadataBitWork primitive K outerBits scalarBits N bits pos hpos ≤ 2268 * dyadicMidpointMetadataBound c K := by
  have hWork := (i.machine K outerBits scalarBits).cachedCallbackWork_state_bound
    (i.fourMidpointMetadataCharge primitive K outerBits scalarBits) (28 * dyadicMidpointMetadataBound c K)
    (i.fourMidpointMetadataCharge_bound primitive c hPrimitive K outerBits scalarBits) N bits
    (i.start K outerBits scalarBits) pos hpos
  have hRank : (i.machine K outerBits scalarBits).rank (i.start K outerBits scalarBits) + 1 ≤ 81 := by
    have h := i.machine_rank K outerBits scalarBits
    omega
  have h := hWork.trans (Nat.mul_le_mul_left (28 * dyadicMidpointMetadataBound c K) hRank)
  have hConstant : (28 * dyadicMidpointMetadataBound c K) * 81 = 2268 * dyadicMidpointMetadataBound c K := by ring
  exact h.trans_eq hConstant

end Blotto.RationalFourInput
namespace Blotto.RationalFourSpec

def midpointMetadataBitWork (i : RationalFourSpec) (primitive : ℕ → ℕ) (K : ℕ)
    (outerBits scalarBits : Fin K → Bool) (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) : ℕ :=
  4 * i.input.fourMidpointMetadataBitWork primitive K outerBits scalarBits N bits pos hpos

theorem midpointMetadataBitWork_bound (i : RationalFourSpec) (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c * w) (K : ℕ) (outerBits scalarBits : Fin K → Bool)
    (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) :
    i.midpointMetadataBitWork primitive K outerBits scalarBits N bits pos hpos ≤ 9072 * dyadicMidpointMetadataBound c K := by
  have h := Nat.mul_le_mul_left 4 (i.input.fourMidpointMetadataBitWork_bound primitive c hPrimitive K outerBits scalarBits N bits pos hpos)
  have hConstant : 4 * (2268 * dyadicMidpointMetadataBound c K) = 9072 * dyadicMidpointMetadataBound c K := by ring
  exact h.trans_eq hConstant

noncomputable def completeProcessingWithMidpointMetadataWork (i : RationalFourSpec) (model : RationalCostModel)
    (primitive : ℕ → ℕ) (copyResources : Bool) (K : ℕ) (outerBits scalarBits : Fin K → Bool)
    (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) : ℕ :=
  i.completeProcessingAllowance model primitive copyResources K outerBits scalarBits N bits pos hpos +
    i.midpointMetadataBitWork primitive K outerBits scalarBits N bits pos hpos

theorem FieldsHeight.completeProcessingWithMidpointMetadataWork_bound {i : RationalFourSpec} {s : ℕ}
    (h : i.FieldsHeight s) (hs : 2 ≤ s) (model : RationalCostModel) (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c * w) (copyResources : Bool) (K : ℕ) (outerBits scalarBits : Fin K → Bool)
    (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) :
    i.completeProcessingWithMidpointMetadataWork model primitive copyResources K outerBits scalarBits N bits pos hpos ≤
      9072 * RationalNestedInput.preparationNumericBitWork c K +
        69175167 * model.rat (RationalFourInput.completeDataWidth (max s (K + 2))) +
          320 * RationalFourInput.fourControlWordHeight (max s (K + 2)) +
            (24 * RationalFourInput.fourControlWordHeight (max s (K + 2)) + 28) * (162 + 2 * (N - pos)) +
              9072 * dyadicMidpointMetadataBound c K :=
  Nat.add_le_add (h.completeProcessingAllowance_bound hs model primitive c hPrimitive copyResources K outerBits scalarBits N bits pos hpos)
    (i.midpointMetadataBitWork_bound primitive c hPrimitive K outerBits scalarBits N bits pos hpos)

end Blotto.RationalFourSpec
