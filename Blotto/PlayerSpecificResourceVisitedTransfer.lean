import Blotto.PlayerSpecificFiniteResourceSourceCost

/-! Monotone transfer of proof-only reached-state certificates. -/
namespace Blotto.PlayerSpecificResourceVisitedTransfer
open PlayerSpecificAlgebraicResourceState PlayerSpecificAlgebraicResourceRequest
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem mono {N : ℕ} (model : RationalCostModel) (p : PlayerSpecificAlgebraicInitialVector.Result N)
    (P Q : State N → Prop) (hPQ : ∀ s,P s → Q s) (fuel : ℕ) (s : State N)
    (h : PlayerSpecificResourceVisitedStates.All model p P fuel s) :
    PlayerSpecificResourceVisitedStates.All model p Q fuel s := by
  induction fuel generalizing s with
  | zero => exact hPQ s h
  | succ fuel ih =>
    refine ⟨hPQ s h.1,?_⟩
    cases hr : request model p s with
    | none => trivial
    | some f =>
      intro upper
      exact ih (advance model p s f upper) (PlayerSpecificResourceVisitedStates.next model p P fuel s h f hr upper)

end Blotto.PlayerSpecificResourceVisitedTransfer
