import Blotto.PlayerSpecificEventDistance

/-! Uniform whole-event leaf errors compose through the exact native
resource law. Only actual reached leaves are required. -/
namespace Blotto.PlayerSpecificIdealResourceEventTransfer
open MeasureTheory PlayerSpecificAlgebraicResourceState
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem bound {N M : ℕ} (model : RationalCostModel) (p : PlayerSpecificAlgebraicInitialVector.Result N) (x : ℝ)
    (u l : State N → Mixed M) (C : ℕ) (s : State N) (hn : PlayerSpecificResourceIdealMean.Normalized model p x C s) (E : ℝ)
    (hl : PlayerSpecificResourceIdealLeaves.ForLeaves model p (fun t => PlayerSpecificEventDistance.Bound (u t) (l t) E) C s) :
    PlayerSpecificEventDistance.Bound (PlayerSpecificResourceIdealLaw.law model p x u C s hn)
      (PlayerSpecificResourceIdealLaw.law model p x l C s hn) E := by
  intro A hA
  rw [PlayerSpecificResourceIdealLaw.event model p x u C s hn A hA,
    PlayerSpecificResourceIdealLaw.event model p x l C s hn A hA]
  apply PlayerSpecificResourceIdealLeaves.mean_error model p x _ _ E C s hn
  exact PlayerSpecificResourceIdealLeaves.mono model p _ _ C s hl (fun t ht => ht A hA)

end Blotto.PlayerSpecificIdealResourceEventTransfer
