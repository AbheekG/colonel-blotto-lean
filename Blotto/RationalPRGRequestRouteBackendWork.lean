import Blotto.RationalPRGRouteBackendWork
import Blotto.RationalPRGRequestComponentWork
import Blotto.RationalPRGGroupTableConstructionWork

/-! The reached terminal backend ledger follows the retained request gate.
Its bound uses the exact parsed input width/field count. This is a component
bound; a uniform incoming-length/full-time composition remains separate. -/

namespace Blotto.RationalPRGBinaryRequest

noncomputable def routeBackendWork (model : RationalCostModel) (primitive : ℕ → ℕ) (rich : Bool) (frame seed : List Bool) : ℕ :=
  acceptedComponentWork (fun {n} i K bits =>
    RationalPRGOriginalInput.selectedRouteBackendWork (n := n) i model primitive rich K bits) frame seed

def routeBackendBound (model : RationalCostModel) (c : ℕ) (frame : List Bool) : ℕ :=
  match readWords frame with
  | none => 0
  | some parsed =>
      let s := 3 + parsed.1.2.originalInputWordWidth
      RationalTerminalLotto.terminalRouteBackendBound model c parsed.1.1 s
        (RationalLottoResourceSystem.bitRouteSlotWidth parsed.1.1 s)

theorem routeBackendWork_bound (model : RationalCostModel) (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c * w) (rich : Bool) (frame seed : List Bool) :
    routeBackendWork model primitive rich frame seed ≤ routeBackendBound model c frame := by
  unfold routeBackendBound
  cases hParsed : readWords frame with
  | none => unfold routeBackendWork acceptedComponentWork; rw [hParsed]
  | some parsed =>
    apply acceptedComponentWork_bound
    intro input words suffix hRead bits
    rw [hParsed] at hRead
    cases Option.some.inj hRead
    exact input.2.selectedRouteBackendWork_bound model primitive c hPrimitive rich words.precision bits

noncomputable def executionWithRouteBackendWork (model : RationalCostModel) (primitive : ℕ → ℕ) (c : ℕ)
    (copyResources rich : Bool) (frame seed : List Bool) : ℕ :=
  executionWithGroupTableConstructionWork model primitive c copyResources rich frame seed + routeBackendWork model primitive rich frame seed

theorem executionWithRouteBackendWork_bound (model : RationalCostModel) (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c * w) (copyResources rich : Bool) (frame seed : List Bool) :
    executionWithRouteBackendWork model primitive c copyResources rich frame seed ≤
      executionFrameBound model c copyResources frame.length seed.length + gameMetadataBound c frame.length +
        decoderMetadataBound c frame.length + outputMetadataFrameBound c frame.length +
          9072 * dyadicMidpointMetadataBound c (frame.length + 6) + positionReaderFrameBound c frame.length +
            scalarReaderFrameBound c frame.length + constructionMetadataFrameBound c frame.length +
              entryConstructionMetadataFrameBound c frame.length + packetRoutingMetadataFrameBound c frame.length +
                packingCopyFrameBound c frame.length + groupTableConstructionFrameBound c frame.length + routeBackendBound model c frame :=
  Nat.add_le_add (executionWithGroupTableConstructionWork_bound model primitive c hPrimitive copyResources rich frame seed)
    (routeBackendWork_bound model primitive c hPrimitive rich frame seed)

theorem routeBackendWork_run_failure (model : RationalCostModel) (primitive : ℕ → ℕ) (rich : Bool) (frame seed : List Bool)
    (h : run rich frame seed = none) : routeBackendWork model primitive rich frame seed = 0 :=
  acceptedComponentWork_run_failure _ rich frame seed h

end Blotto.RationalPRGBinaryRequest
