import Blotto.BinaryGroupRouteEmissionWork

/-! Actual cached original-request route coefficients derive their stored
heights from reached lengths and retained packing totals. No coefficient/
route-height oracle or reciprocal minimum-total promise is supplied. -/

namespace Blotto.BinaryCachedRouteHeight
open BinaryRationalNormalization BinaryRationalEncoding BinaryCachedTerminalPreparation
open BinaryPRGResourceWork BinaryPRGTerminalWork BinaryCachedGroupInputHeight

theorem reached_route_height {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool) (N : ℕ) (bits : Fin N → Bool)
    (state : BinaryResourcePair.Certified (resourceInput request rich).length)
    (h : (resourceWork request rich N bits).1.1 = some state) (j : Fin n) :
    RationalHeight (value ((prepare (terminalInput request rich state)).routes.read j).2) (expressionHeightBudget (inputHeight request) 1) := by
  let cached := prepare (terminalInput request rich state)
  have hC := terminal_canonical request rich state
  have hs : 3 ≤ inputHeight request := by unfold inputHeight; omega
  have hLength : ∀ j, RationalHeight (value ((terminalInput request rich state).length.read j)) (inputHeight request) := by
    intro j; exact (length_height request rich j).mono (by have hd := lattice_height_original request; omega)
  have hTotal : ∀ g, RationalHeight (value (cached.packing.read g).2) (inputHeight request) := by
    intro g
    have ht := cached_total_height request rich N bits state h g
    change RationalHeight (value (cached.totals.read g)) (inputHeight request) at ht
    rw [cached.totals_eq,FixedArrayTable.read_ofFn] at ht
    exact ht
  change RationalHeight (value (cached.routes.read j).2) _
  rw [cached.routes_eq]
  exact BinaryGroupRouteEmissionWork.prepare_height _ _ hC.2.1
    (BinaryCachedTerminalWork.Prepared.total_canonical cached hC) _ hs hLength hTotal j

end Blotto.BinaryCachedRouteHeight
