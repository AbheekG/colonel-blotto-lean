import Blotto.DyadicMidpointLaw
import Blotto.NestedLocation
import Blotto.ThresholdCDF

/-! The first nested case's rational location map driven by K fair bits.
Its location CDF has error at most 1/(2*2^K), and every location lies in [0,t].
The error of averaging its location-dependent allocation family is separate. -/

namespace Blotto.NestedInput
open MeasureTheory Set

theorem location_thresholds (i : NestedInput) (z : ℝ) :
    ∃ q : ℝ, ∀ x ∈ Icc (0 : ℝ) 1, i.location x ≤ z ↔ x ≤ q := by
  by_cases hz : z < 0
  · refine ⟨-1, ?_⟩
    intro x hx
    have hl := i.location_bounds hx
    constructor <;> intro h <;> linarith [hx.1]
  · have hz0 : 0 ≤ z := le_of_not_gt hz
    by_cases hzt : z ≤ i.t
    · exact ⟨i.locationCDF z, fun _ hx => i.location_threshold hx ⟨hz0, hzt⟩⟩
    · refine ⟨1, ?_⟩
      intro x hx
      have hl := i.location_bounds hx
      have htz := le_of_lt (lt_of_not_ge hzt)
      exact ⟨fun _ => hx.2, fun _ => hl.2.trans htz⟩

noncomputable def dyadicLocationLaw (i : NestedInput) (K : ℕ) : ProbabilityMeasure ℝ :=
  (dyadicMidpointLaw K).map i.location

theorem dyadicLocationLaw_CDF_error (i : NestedInput) (K : ℕ) :
    RealCDFClose (i.dyadicLocationLaw K) i.locationLaw (1 / (2 * (2 : ℝ) ^ K)) := by
  have hm : ∀ᵐ x ∂(dyadicMidpointLaw K : Measure ℝ), x ∈ Icc (0 : ℝ) 1 := by
    rw [dyadicMidpointLaw_eq]
    exact midpointLaw_supported _
  exact (dyadicMidpointLaw_CDF_error K).threshold_map i.location i.measurable_location (Icc 0 1)
    hm unitUniform_supported i.location_thresholds

theorem dyadicLocationLaw_supported (i : NestedInput) (K : ℕ) :
    ∀ᵐ s ∂(i.dyadicLocationLaw K : Measure ℝ), s ∈ Icc 0 i.t := by
  have hm : ∀ᵐ x ∂(dyadicMidpointLaw K : Measure ℝ), x ∈ Icc (0 : ℝ) 1 := by
    rw [dyadicMidpointLaw_eq]
    exact midpointLaw_supported _
  change ∀ᵐ s ∂Measure.map i.location (dyadicMidpointLaw K : Measure ℝ), 0 ≤ s ∧ s ≤ i.t
  rw [ae_map_iff i.measurable_location.aemeasurable measurableSet_Icc]
  exact hm.mono (fun _ hx => i.location_bounds hx)

theorem dyadicLocation_point_bounds (i : NestedInput) (K : ℕ) (bits : Fin K → Bool) :
    i.location (dyadicMidpointSample K bits) ∈ Icc 0 i.t :=
  i.location_bounds ⟨le_of_lt (dyadicMidpointSample_bounds K bits).1,
    le_of_lt (dyadicMidpointSample_bounds K bits).2⟩

end Blotto.NestedInput
