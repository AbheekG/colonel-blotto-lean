import Blotto.SegmentLottery
import Blotto.WeightedIntervals
import Blotto.ThreeMarginals

/-! The exact Lebesgue density of a non-atomic affine observation of a finite
segment lottery. Constant projections have zero weight by the actual marginal. -/

namespace Blotto
open MeasureTheory Set Filter
open scoped BigOperators

theorem weighted_affine_sorted (a b q : ℝ) (hq : 0 ≤ q) (hzero : a = b → q = 0) :
    ENNReal.ofReal q • (affineUniform a b : Measure ℝ) =
      ENNReal.ofReal (q / |b - a|) • rawInterval (min a b) (max a b) := by
  rcases lt_trichotomy a b with h | h | h
  · rw [min_eq_left (le_of_lt h), max_eq_right (le_of_lt h), abs_of_pos (sub_pos.mpr h)]
    exact affineUniform_scaled_interval h hq
  · rw [hzero h]
    simp
  · rw [min_eq_right (le_of_lt h), max_eq_left (le_of_lt h), abs_of_neg (sub_neg.mpr h)]
    have he : -(b - a) = a - b := by ring
    rw [he]
    exact affineUniform_scaled_interval_reverse h hq

noncomputable def intervalDensity (a b r : ℝ) : ℝ → ENNReal :=
  (Icc a b).indicator (fun _ => ENNReal.ofReal r)

theorem measurable_intervalDensity (a b r : ℝ) : Measurable (intervalDensity a b r) :=
  measurable_const.indicator measurableSet_Icc

theorem intervalDensity_measure (a b r : ℝ) :
    volume.withDensity (intervalDensity a b r) = ENNReal.ofReal r • rawInterval a b := by
  rw [intervalDensity, withDensity_indicator measurableSet_Icc, withDensity_const]
  rfl

namespace SegmentLottery

noncomputable def slotDensity {n k : ℕ} (l : SegmentLottery n k) (f : AffineProbe n) (i : Fin k) : ℝ → ENNReal :=
  intervalDensity (min (f.value (l.P i)) (f.value (l.Q i)))
    (max (f.value (l.P i)) (f.value (l.Q i)))
    (l.weight i / |f.value (l.Q i) - f.value (l.P i)|)

noncomputable def auxiliaryDensity {n k : ℕ} (l : SegmentLottery n k) (f : AffineProbe n) : ℝ → ENNReal :=
  ∑ i, l.slotDensity f i

theorem measurable_slotDensity {n k : ℕ} (l : SegmentLottery n k) (f : AffineProbe n) (i : Fin k) :
    Measurable (l.slotDensity f i) := measurable_intervalDensity _ _ _

theorem measurable_auxiliaryDensity {n k : ℕ} (l : SegmentLottery n k) (f : AffineProbe n) :
    Measurable (l.auxiliaryDensity f) := by
  change Measurable (fun z => l.auxiliaryDensity f z)
  simp only [auxiliaryDensity, Finset.sum_apply]
  exact Finset.measurable_sum Finset.univ (fun i _ => l.measurable_slotDensity f i)

theorem probe_withDensity {n k : ℕ} (l : SegmentLottery n k) (f : AffineProbe n) (d : ℝ)
    (hm : Measure.map f.value (l.law : Measure (Allocation n)) = uniformLaw d) :
    Measure.map f.value (l.law : Measure (Allocation n)) = volume.withDensity (l.auxiliaryDensity f) := by
  have he : l.auxiliaryDensity f = ∑' i, l.slotDensity f i := by simp [auxiliaryDensity, tsum_fintype]
  rw [he, withDensity_tsum (fun i => l.measurable_slotDensity f i), l.probe_measure]
  congr 1
  funext i
  rw [slotDensity, intervalDensity_measure]
  exact weighted_affine_sorted _ _ _ (l.nonnegative i) (fun h => l.constant_probe_weight_zero f d hm i h)

/-- The auxiliary density equals the normalized uniform density almost
 everywhere, including all zero-weight/collapsed entries. -/
theorem auxiliaryDensity_uniform {n k : ℕ} (l : SegmentLottery n k) (f : AffineProbe n)
    {d : ℝ} (hd : 0 < d)
    (hm : Measure.map f.value (l.law : Measure (Allocation n)) = uniformLaw d) :
    l.auxiliaryDensity f =ᵐ[(volume : Measure ℝ)] intervalDensity 0 d (1 / d) := by
  apply (withDensity_eq_iff_of_sigmaFinite (l.measurable_auxiliaryDensity f).aemeasurable
    (measurable_intervalDensity 0 d (1 / d)).aemeasurable).mp
  rw [← l.probe_withDensity f d hm, hm, intervalDensity_measure, ← uniformLaw_density hd]

end SegmentLottery
end Blotto
