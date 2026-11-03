import Blotto.PlayerSpecificResourceIdealLaw

/-! A complete terminal sample uses a fresh suffix after the actual flat
resource packet. Its whole measurable-event error to exact resource
choices is bounded independently of its internal coordinate dependence. -/
namespace Blotto.PlayerSpecificResourceContinuationLaw
open MeasureTheory PlayerSpecificAlgebraicResourceState
set_option autoImplicit false
set_option maxHeartbeats 2500000

noncomputable def law {N M : ℕ} (model : RationalCostModel) (p : PlayerSpecificAlgebraicInitialVector.Result N)
    (H C S : ℕ) (s : State N) (draw : State N → (Fin S → Bool) → Allocation M) : Mixed M :=
  (fairBitLaw (C*H+S)).map (fun bits =>
    draw (PlayerSpecificFiniteResourceLoop.run model p H C s
      (PlayerSpecificFiniteResourceLoop.blocks C H (firstBitBlock (C*H) S bits))).1 (secondBitBlock (C*H) S bits))

theorem event {N M : ℕ} (model : RationalCostModel) (p : PlayerSpecificAlgebraicInitialVector.Result N)
    (H C S : ℕ) (s : State N) (draw : State N → (Fin S → Bool) → Allocation M)
    (A : Set (Allocation M)) (hA : MeasurableSet A) :
    (law model p H C S s draw : Measure (Allocation M)).real A=
      PlayerSpecificResourceExpectation.mean model p H C s
        (fun t => ((fairBitLaw S).map (draw t) : Measure (Allocation M)).real A) := by
  classical
  rw [law,PlayerSpecificFairAveraging.event _ _ A hA]
  rw [PlayerSpecificFairBitBlocks.integral_blocks (C*H) S (fun resource terminal =>
    if draw (PlayerSpecificFiniteResourceLoop.run model p H C s (PlayerSpecificFiniteResourceLoop.blocks C H resource)).1 terminal ∈ A
      then (1:ℝ) else 0)]
  unfold PlayerSpecificResourceExpectation.mean
  simp_rw [PlayerSpecificFairAveraging.event S _ A hA]

theorem event_error {N M : ℕ} (model : RationalCostModel) (p : PlayerSpecificAlgebraicInitialVector.Result N)
    (x : ℝ) (hc : PlayerSpecificAlgebraicResourceLoop.Context p x) (H C S : ℕ) (s : State N) (hs : Valid p x s)
    (draw : State N → (Fin S → Bool) → Allocation M) (A : Set (Allocation M)) (hA : MeasurableSet A) :
    |(law model p H C S s draw : Measure (Allocation M)).real A-
      (PlayerSpecificResourceIdealLaw.law model p x (fun t => (fairBitLaw S).map (draw t)) C s
        (PlayerSpecificResourceIdealMean.of_valid model p x hc C s hs) : Measure (Allocation M)).real A| ≤ (C:ℝ)/(2:ℝ)^H := by
  rw [event model p H C S s draw A hA,PlayerSpecificResourceIdealLaw.event _ _ _ _ _ _ _ A hA]
  exact PlayerSpecificResourceDiscrepancy.actual_valid model p x hc H C s hs _
    (fun t => PlayerSpecificResourceIdealLaw.event_bounds ((fairBitLaw S).map (draw t)) A)

end Blotto.PlayerSpecificResourceContinuationLaw
