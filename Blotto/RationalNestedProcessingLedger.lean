import Blotto.RationalNestedDataOutputLedger
import Blotto.RationalNestedControlWords
import Blotto.CachedControlIndexedBound

/-! Local data/primitive and Boolean-control components combine at the same
reader position. Later maps, fallback and address/metadata/backend/allocator/
ownership are separate; this is not a full PRG execution-time certificate. -/

namespace Blotto.RationalNestedResourceSystem

def localBooleanControlWork (i : RationalNestedResourceSystem) (K : ℕ) (outerBits scalarBits : Fin K → Bool)
    (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) : ℕ :=
  (i.machine K outerBits scalarBits).cachedControlWork (fun _ => true) (fun w => 4 * w) FixedWordCoin.bodyAllowance
    N bits (.state i.samplingStart) pos hpos

theorem FieldsHeight.localBooleanControlWork_bound {i : RationalNestedResourceSystem} {s : ℕ}
    (h : i.FieldsHeight s) (hs : 2 ≤ s) (K : ℕ) (hPrecision : K + 2 ≤ s) (outerBits scalarBits : Fin K → Bool)
    (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) :
    i.localBooleanControlWork K outerBits scalarBits N bits pos hpos ≤
      76 * localControlWordHeight s + (24 * localControlWordHeight s + 28) * (40 + 2 * (N - pos)) := by
  have hp := (i.machine K outerBits scalarBits).cachedControlWork_state_bound_under
    (i.LocalCallbackInvariant s) (localControlWordHeight s)
    (fun state hState => h.localCallback_wordsHeight hs K hPrecision outerBits scalarBits state hState)
    (h.localCallback_closed hs K hPrecision outerBits scalarBits)
    N bits i.samplingStart h.localCallback_start 19 (i.machine_rank K outerBits scalarBits) pos hpos
  have he : 4 * localControlWordHeight s * 19 +
      (24 * localControlWordHeight s + 28) * (2 * 19 + 2 * (N - pos) + 2) =
        76 * localControlWordHeight s + (24 * localControlWordHeight s + 28) * (40 + 2 * (N - pos)) := by ring
  exact hp.trans_eq he

noncomputable def localProcessingWork (i : RationalNestedResourceSystem) (model : RationalCostModel)
    (primitive : ℕ → ℕ) (copyResources : Bool) (K : ℕ) (outerBits scalarBits : Fin K → Bool)
    (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) : ℕ :=
  i.localDataOutputBitWork model primitive copyResources K outerBits scalarBits N bits pos hpos +
    i.localBooleanControlWork K outerBits scalarBits N bits pos hpos

theorem FieldsHeight.localProcessingWork_bound {i : RationalNestedResourceSystem} {s : ℕ}
    (h : i.FieldsHeight s) (hs : 2 ≤ s) (model : RationalCostModel) (primitive : ℕ → ℕ)
    (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w) (copyResources : Bool) (K : ℕ)
    (outerBits scalarBits : Fin K → Bool) (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) :
    i.localProcessingWork model primitive copyResources K outerBits scalarBits N bits pos hpos ≤
      58 * RationalNestedInput.preparationNumericBitWork c K +
        498000 * model.rat (localDataOutputWidth (max s (K + 2))) +
          76 * localControlWordHeight (max s (K + 2)) +
            (24 * localControlWordHeight (max s (K + 2)) + 28) * (40 + 2 * (N - pos)) := by
  have hW := h.mono (le_max_left s (K + 2))
  have hw := hs.trans (le_max_left s (K + 2))
  have hPrecision := le_max_right s (K + 2)
  have hd := hW.localDataOutputBitWork_bound hw model primitive c hPrimitive copyResources K hPrecision
    outerBits scalarBits N bits pos hpos
  have hc := hW.localBooleanControlWork_bound hw K hPrecision outerBits scalarBits N bits pos hpos
  unfold localProcessingWork
  omega

end Blotto.RationalNestedResourceSystem
