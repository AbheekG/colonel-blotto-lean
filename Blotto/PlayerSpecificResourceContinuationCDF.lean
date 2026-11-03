import Blotto.PlayerSpecificResourceContinuationLaw
import Blotto.PlayerSpecificResourceIdealMoments
import Blotto.AllocationCDFDistance

/-! Marginal errors of complete terminal samples compose through the
actual resource controller. Affine dependence on each resource coordinate
is averaged exactly by the checked native expectation invariant. -/
namespace Blotto.PlayerSpecificResourceContinuationCDF
open MeasureTheory PlayerSpecificAlgebraicResourceState
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem cdf_event {N : ℕ} (l : Mixed N) (j : Fin N) (z : ℝ) :
    closedCDF l j z=(l : Measure (Allocation N)).real ((fun y : Allocation N => y j) ⁻¹' Set.Iic z) := by
  change (Measure.map (fun y : Allocation N => y j) (l : Measure (Allocation N))).real (Set.Iic z)=_
  exact map_measureReal_apply (measurable_pi_apply j) measurableSet_Iic

theorem ideal_error {N : ℕ} (model : RationalCostModel) (p : PlayerSpecificAlgebraicInitialVector.Result N)
    (x : ℝ) (hc : PlayerSpecificAlgebraicResourceLoop.Context p x) (C : ℕ) (s : State N) (hs : Valid p x s)
    (leaf : State N → Mixed N) (target : Mixed N) (a b : Fin N → ℝ → ℝ) (E : ℝ)
    (ht : ∀ j z,closedCDF target j z=a j z+b j z*eval s x j)
    (hl : ∀ j z,PlayerSpecificResourceIdealLeaves.ForLeaves model p
      (fun t => |closedCDF (leaf t) j z-(a j z+b j z*eval t x j)| ≤ E) C s) :
    CDFClose (PlayerSpecificResourceIdealLaw.law model p x leaf C s
      (PlayerSpecificResourceIdealMean.of_valid model p x hc C s hs)) target E := by
  intro j z
  have he := PlayerSpecificResourceIdealLaw.event model p x leaf C s
    (PlayerSpecificResourceIdealMean.of_valid model p x hc C s hs)
    ((fun y : Allocation N => y j) ⁻¹' Set.Iic z) ((measurable_pi_apply j) measurableSet_Iic)
  simp_rw [←cdf_event] at he
  have h := PlayerSpecificResourceIdealLeaves.mean_error model p x (fun t => closedCDF (leaf t) j z)
    (fun t => a j z+b j z*eval t x j) E C s (PlayerSpecificResourceIdealMean.of_valid model p x hc C s hs) (hl j z)
  rw [←he,PlayerSpecificResourceIdealMoments.affine model p x hc C s hs (a j z) (b j z) j] at h
  rw [ht]
  exact h

theorem resource_error {N M : ℕ} (model : RationalCostModel) (p : PlayerSpecificAlgebraicInitialVector.Result N)
    (x : ℝ) (hc : PlayerSpecificAlgebraicResourceLoop.Context p x) (H C S : ℕ) (s : State N) (hs : Valid p x s)
    (draw : State N → (Fin S → Bool) → Allocation M) :
    CDFClose (PlayerSpecificResourceContinuationLaw.law model p H C S s draw)
      (PlayerSpecificResourceIdealLaw.law model p x (fun t => (fairBitLaw S).map (draw t)) C s
        (PlayerSpecificResourceIdealMean.of_valid model p x hc C s hs)) ((C:ℝ)/(2:ℝ)^H) := by
  intro j z
  rw [cdf_event,cdf_event]
  exact PlayerSpecificResourceContinuationLaw.event_error model p x hc H C S s hs draw _ ((measurable_pi_apply j) measurableSet_Iic)

theorem CDF_error {N : ℕ} (model : RationalCostModel) (p : PlayerSpecificAlgebraicInitialVector.Result N)
    (x : ℝ) (hc : PlayerSpecificAlgebraicResourceLoop.Context p x) (H C S : ℕ) (s : State N) (hs : Valid p x s)
    (draw : State N → (Fin S → Bool) → Allocation N) (target : Mixed N) (a b : Fin N → ℝ → ℝ) (E : ℝ)
    (ht : ∀ j z,closedCDF target j z=a j z+b j z*eval s x j)
    (hl : ∀ j z,PlayerSpecificResourceIdealLeaves.ForLeaves model p
      (fun t => |closedCDF ((fairBitLaw S).map (draw t)) j z-(a j z+b j z*eval t x j)| ≤ E) C s) :
    CDFClose (PlayerSpecificResourceContinuationLaw.law model p H C S s draw) target ((C:ℝ)/(2:ℝ)^H+E) :=
  (resource_error model p x hc H C S s hs draw).triangle
    (ideal_error model p x hc C s hs (fun t => (fairBitLaw S).map (draw t)) target a b E ht hl)

end Blotto.PlayerSpecificResourceContinuationCDF
