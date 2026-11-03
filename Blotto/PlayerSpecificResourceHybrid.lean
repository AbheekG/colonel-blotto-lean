import Blotto.PlayerSpecificBinaryEventTransfer

/-! A fixed exact-choice terminal hybrid is independent of H. Uniform
leaf event bounds and the actual resource controller give one total event
bound for every finite coin precision. -/
namespace Blotto.PlayerSpecificResourceHybrid
open MeasureTheory PlayerSpecificAlgebraicResourceState
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem event_bound {N M : ℕ} (model : RationalCostModel) (p : PlayerSpecificAlgebraicInitialVector.Result N)
    (x : ℝ) (hc : PlayerSpecificAlgebraicResourceLoop.Context p x) (C : ℕ) (s : State N) (hs : Valid p x s)
    (S : ℕ → ℕ) (draw : (H : ℕ) → State N → (Fin (S H) → Bool) → Allocation M)
    (leaf : State N → Mixed M) (E : ℕ)
    (hl : ∀ H,PlayerSpecificResourceIdealLeaves.ForLeaves model p
      (fun t => PlayerSpecificEventDistance.Bound ((fairBitLaw (S H)).map (draw H t)) (leaf t) ((E:ℝ)/(2:ℝ)^H)) C s) :
    ∀ H,PlayerSpecificEventDistance.Bound (PlayerSpecificResourceContinuationLaw.law model p H C (S H) s (draw H))
      (PlayerSpecificResourceIdealLaw.law model p x leaf C s (PlayerSpecificResourceIdealMean.of_valid model p x hc C s hs))
        (((C+E:ℕ):ℝ)/(2:ℝ)^H) := by
  intro H
  have hR : PlayerSpecificEventDistance.Bound (PlayerSpecificResourceContinuationLaw.law model p H C (S H) s (draw H))
      (PlayerSpecificResourceIdealLaw.law model p x (fun t => (fairBitLaw (S H)).map (draw H t)) C s
        (PlayerSpecificResourceIdealMean.of_valid model p x hc C s hs)) ((C:ℝ)/(2:ℝ)^H) :=
    fun A hA => PlayerSpecificResourceContinuationLaw.event_error model p x hc H C (S H) s hs (draw H) A hA
  have hT := PlayerSpecificIdealResourceEventTransfer.bound model p x (fun t => (fairBitLaw (S H)).map (draw H t)) leaf C s
    (PlayerSpecificResourceIdealMean.of_valid model p x hc C s hs) ((E:ℝ)/(2:ℝ)^H) (hl H)
  have h := PlayerSpecificEventDistance.triangle _ _ _ _ _ hR hT
  have he : (C:ℝ)/(2:ℝ)^H+(E:ℝ)/(2:ℝ)^H=((C+E:ℕ):ℝ)/(2:ℝ)^H := by push_cast; ring
  rw [he] at h
  exact h

end Blotto.PlayerSpecificResourceHybrid
