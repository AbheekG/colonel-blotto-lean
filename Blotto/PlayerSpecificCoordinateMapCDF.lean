import Blotto.RealCDFDistance
import Blotto.AllocationCDFDistance

/-! A whole-allocation map whose individual coordinates are affine
images of one input coordinate preserves marginal CDF error. Constant
padding, coordinate restoration and direct proportional leaves are included. -/
namespace Blotto.PlayerSpecificCoordinateMapCDF
open MeasureTheory
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem marginal {N M : ℕ} (f : Allocation N → Allocation M) (hf : Measurable f)
    (index : Fin M → Fin N) (left right : Fin M → ℝ)
    (he : ∀ y j,f y j=affineLine (left j) (right j) (y (index j))) (l : Mixed N) (j : Fin M) :
    marginal (l.map f) j=(marginal l (index j)).map (affineLine (left j) (right j)) := by
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.map (fun y : Allocation M => y j) (Measure.map f (l : Measure (Allocation N)))=
    Measure.map (affineLine (left j) (right j)) (Measure.map (fun y : Allocation N => y (index j)) (l : Measure (Allocation N)))
  rw [Measure.map_map (measurable_pi_apply j) hf,
    Measure.map_map (measurable_affineLine _ _) (measurable_pi_apply (index j))]
  congr 1
  funext y
  exact he y j

theorem CDF_error {N M : ℕ} (f : Allocation N → Allocation M) (hf : Measurable f)
    (index : Fin M → Fin N) (left right : Fin M → ℝ)
    (he : ∀ y j,f y j=affineLine (left j) (right j) (y (index j)))
    (u l : Mixed N) (E : ℝ) (h : CDFClose u l E) : CDFClose (u.map f) (l.map f) E := by
  intro j z
  unfold closedCDF
  rw [marginal f hf index left right he u j,marginal f hf index left right he l j]
  exact (show RealCDFClose (Blotto.marginal u (index j)) (Blotto.marginal l (index j)) E from fun t => h (index j) t).affine
    (left j) (right j) z

end Blotto.PlayerSpecificCoordinateMapCDF
