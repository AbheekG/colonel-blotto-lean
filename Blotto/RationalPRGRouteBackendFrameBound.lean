import Blotto.RationalRouteBackendBoundMonotone

/-! The terminal route-backend ledger now has a uniform incoming-frame
envelope. Existing parse bounds control dimensions, game words and slot width.
This is a symbolic component/full-ledger envelope with explicit Rat/primitive
parameters; concrete complete time/space contracts are still separate. -/

namespace Blotto.RationalPRGBinaryRequest

def routeBackendFrameBound (model : RationalCostModel) (c length : ℕ) : ℕ :=
  let s := 3 + (length + 2) * (4 * length + 13)
  RationalTerminalLotto.terminalRouteBackendBound model c length s
    (RationalLottoResourceSystem.bitRouteSlotWidth length s)

theorem routeBackendBound_frame_bound (model : RationalCostModel) (c : ℕ) (frame : List Bool) :
    routeBackendBound model c frame ≤ routeBackendFrameBound model c frame.length := by
  unfold routeBackendBound
  cases hParsed : readWords frame with
  | none => exact Nat.zero_le _
  | some parsed =>
    rcases parsed with ⟨input, words, suffix⟩
    have hSize := readWords_bounds frame input words suffix hParsed
    have hInput := readWords_inputWordWidth frame input words suffix hParsed
    have hWords := Nat.add_le_add_left hInput 3
    exact RationalTerminalLotto.terminalRouteBackendBound_mono model c hSize.1 hWords
      (RationalLottoResourceSystem.bitRouteSlotWidth_mono hSize.1 hWords)

theorem routeBackendWork_frame_bound (model : RationalCostModel) (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c * w) (rich : Bool) (frame seed : List Bool) :
    routeBackendWork model primitive rich frame seed ≤ routeBackendFrameBound model c frame.length :=
  (routeBackendWork_bound model primitive c hPrimitive rich frame seed).trans (routeBackendBound_frame_bound model c frame)

theorem executionWithRouteBackendWork_frame_bound (model : RationalCostModel) (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c * w) (copyResources rich : Bool) (frame seed : List Bool) :
    executionWithRouteBackendWork model primitive c copyResources rich frame seed ≤
      executionFrameBound model c copyResources frame.length seed.length + gameMetadataBound c frame.length +
        decoderMetadataBound c frame.length + outputMetadataFrameBound c frame.length +
          9072 * dyadicMidpointMetadataBound c (frame.length + 6) + positionReaderFrameBound c frame.length +
            scalarReaderFrameBound c frame.length + constructionMetadataFrameBound c frame.length +
              entryConstructionMetadataFrameBound c frame.length + packetRoutingMetadataFrameBound c frame.length +
                packingCopyFrameBound c frame.length + groupTableConstructionFrameBound c frame.length + routeBackendFrameBound model c frame.length :=
  (executionWithRouteBackendWork_bound model primitive c hPrimitive copyResources rich frame seed).trans
    (Nat.add_le_add_left (routeBackendBound_frame_bound model c frame) _)

end Blotto.RationalPRGBinaryRequest
