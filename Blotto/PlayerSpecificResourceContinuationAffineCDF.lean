import Blotto.PlayerSpecificResourceContinuationCDF

/-! Complete sampler CDF comparison to an affine resource formula.
This version needs no supplied target whole-allocation law. -/
namespace Blotto.PlayerSpecificResourceContinuationAffineCDF
open MeasureTheory PlayerSpecificAlgebraicResourceState
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem marginal_error {N M : ℕ} (model : RationalCostModel) (p : PlayerSpecificAlgebraicInitialVector.Result N)
    (x : ℝ) (hc : PlayerSpecificAlgebraicResourceLoop.Context p x) (H C S : ℕ) (s : State N) (hs : Valid p x s)
    (draw : State N → (Fin S → Bool) → Allocation M) (j : Fin M) (k : Fin N) (z a b E : ℝ)
    (hl : PlayerSpecificResourceIdealLeaves.ForLeaves model p
      (fun t => |closedCDF ((fairBitLaw S).map (draw t)) j z-(a+b*eval t x k)| ≤ E) C s) :
    |closedCDF (PlayerSpecificResourceContinuationLaw.law model p H C S s draw) j z-(a+b*eval s x k)| ≤
      (C:ℝ)/(2:ℝ)^H+E := by
  let A := (fun y : Allocation M => y j) ⁻¹' Set.Iic z
  have hA : MeasurableSet A := (measurable_pi_apply j) measurableSet_Iic
  have he := PlayerSpecificResourceContinuationLaw.event model p H C S s draw A hA
  dsimp only [A] at he
  simp_rw [←PlayerSpecificResourceContinuationCDF.cdf_event] at he
  have hR := PlayerSpecificResourceDiscrepancy.actual_valid model p x hc H C s hs
    (fun t => closedCDF ((fairBitLaw S).map (draw t)) j z) (fun t => by
      rw [PlayerSpecificResourceContinuationCDF.cdf_event]
      exact PlayerSpecificResourceIdealLaw.event_bounds _ A)
  have hT := PlayerSpecificResourceIdealLeaves.mean_error model p x
    (fun t => closedCDF ((fairBitLaw S).map (draw t)) j z) (fun t => a+b*eval t x k) E C s
    (PlayerSpecificResourceIdealMean.of_valid model p x hc C s hs) hl
  rw [PlayerSpecificResourceIdealMoments.affine model p x hc C s hs a b k] at hT
  rw [he]
  exact (abs_sub_le _ _ _).trans (add_le_add hR hT)

end Blotto.PlayerSpecificResourceContinuationAffineCDF
