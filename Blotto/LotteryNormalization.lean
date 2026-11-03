import Blotto.LotteryDensity
import Blotto.UniformSupport

/-! Conditional segment weights normalize under the actual common uniform
law. Boundary double counting is confined to a measure-zero set. -/

namespace Blotto.SegmentLottery
open MeasureTheory Set Filter

/-- Lebesgue-a.e. density equality transfers to the sampled auxiliary law. -/
theorem conditionalDensity_normalized {n k : ℕ} (l : SegmentLottery n k) (f : AffineProbe n)
    {d : ℝ} (hd : 0 < d)
    (hm : Measure.map f.value (l.law : Measure (Allocation n)) = uniformLaw d) :
    ∀ᵐ z ∂uniformLaw d, ENNReal.ofReal d * l.auxiliaryDensity f z = 1 := by
  have hU : uniformLaw d = volume.withDensity (intervalDensity 0 d (1 / d)) := by
    rw [intervalDensity_measure, ← uniformLaw_density hd]
  have hAC : uniformLaw d ≪ (volume : Measure ℝ) := by
    rw [hU]
    exact withDensity_absolutelyContinuous _ _
  have he := (l.auxiliaryDensity_uniform f hd hm).filter_mono hAC.ae_le
  apply (he.and (uniformLaw_supported d)).mono
  intro z hz
  rw [hz.1]
  simp only [intervalDensity, indicator_of_mem hz.2, one_div, ENNReal.ofReal_inv_of_pos hd]
  exact ENNReal.mul_inv_cancel (ne_of_gt (ENNReal.ofReal_pos.mpr hd)) ENNReal.ofReal_ne_top

/-- The conditional weights also normalize after observing a second actual
allocation law with the same auxiliary uniform distribution. -/
theorem conditionalDensity_sampled {n k m : ℕ} (l : SegmentLottery n k) (f : AffineProbe n)
    (ν : Mixed m) (g : AffineProbe m) {d : ℝ} (hd : 0 < d)
    (hm : Measure.map f.value (l.law : Measure (Allocation n)) = uniformLaw d)
    (hν : Measure.map g.value (ν : Measure (Allocation m)) = uniformLaw d) :
    ∀ᵐ y ∂(ν : Measure (Allocation m)), ENNReal.ofReal d * l.auxiliaryDensity f (g.value y) = 1 := by
  have h := l.conditionalDensity_normalized f hd hm
  rw [← hν] at h
  exact ae_of_ae_map g.measurable.aemeasurable h

end Blotto.SegmentLottery
