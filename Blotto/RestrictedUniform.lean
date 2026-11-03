import Blotto.InverseSegment
import Blotto.LotteryDensity

/-! Restrict a common uniform coordinate to one source segment's interval,
then invert that segment's affine projection. -/

namespace Blotto
open MeasureTheory Set

theorem uniformLaw_restrict_interval {d a b : ℝ} (hd : 0 < d) (ha : 0 ≤ a) (_hab : a ≤ b) (hb : b ≤ d) :
    (uniformLaw d).restrict (Icc a b) = ENNReal.ofReal (1 / d) • rawInterval a b := by
  have hsub : Icc a b ⊆ Icc 0 d := fun x hx => ⟨le_trans ha hx.1, le_trans hx.2 hb⟩
  rw [uniformLaw, Measure.restrict_smul, Measure.restrict_restrict_of_subset hsub,
    one_div, ENNReal.ofReal_inv_of_pos hd]
  rfl

namespace SegmentLottery

noncomputable def auxiliaryInterval {n k : ℕ} (l : SegmentLottery n k) (f : AffineProbe n) (i : Fin k) : Set ℝ :=
  Icc (min (f.value (l.P i)) (f.value (l.Q i))) (max (f.value (l.P i)) (f.value (l.Q i)))

noncomputable def conditionalWeight {n k : ℕ} (l : SegmentLottery n k) (f : AffineProbe n) (d : ℝ) (i : Fin k) : ℝ :=
  d * l.weight i / |f.value (l.Q i) - f.value (l.P i)|

/-- The weighted inverse image of the common uniform reconstructs exactly
this source segment's contribution to its full allocation law. -/
theorem reconstruct_segment {n k : ℕ} (l : SegmentLottery n k) (f : AffineProbe n) {d : ℝ} (hd : 0 < d)
    (hm : Measure.map f.value (l.law : Measure (Allocation n)) = uniformLaw d)
    (i : Fin k) (hP : 0 ≤ f.value (l.P i) ∧ f.value (l.P i) ≤ d)
    (hQ : 0 ≤ f.value (l.Q i) ∧ f.value (l.Q i) ≤ d) :
    ENNReal.ofReal (l.conditionalWeight f d i) •
      Measure.map (l.pointAt f i) ((uniformLaw d).restrict (l.auxiliaryInterval f i)) =
        ENNReal.ofReal (l.weight i) • (segmentLaw (l.P i) (l.Q i) : Measure (Allocation n)) := by
  by_cases hconst : f.value (l.P i) = f.value (l.Q i)
  · have hw := l.constant_probe_weight_zero f d hm i hconst
    simp [conditionalWeight, hw]
  · have ha : 0 ≤ min (f.value (l.P i)) (f.value (l.Q i)) := le_min hP.1 hQ.1
    have hb : max (f.value (l.P i)) (f.value (l.Q i)) ≤ d := max_le hP.2 hQ.2
    have hlen : 0 < |f.value (l.Q i) - f.value (l.P i)| :=
      abs_pos.mpr (sub_ne_zero.mpr (Ne.symm hconst))
    have hw : 0 ≤ l.conditionalWeight f d i := by
      dsimp [conditionalWeight]
      exact div_nonneg (mul_nonneg (le_of_lt hd) (l.nonnegative i)) (le_of_lt hlen)
    have hc : l.conditionalWeight f d i * (1 / d) =
        l.weight i / |f.value (l.Q i) - f.value (l.P i)| := by
      dsimp [conditionalWeight]
      field_simp [ne_of_gt hd, ne_of_gt hlen]
    have hsegment := congrArg (Measure.map (l.pointAt f i))
      (weighted_affine_sorted (f.value (l.P i)) (f.value (l.Q i)) (l.weight i) (l.nonnegative i)
        (fun h => (hconst h).elim))
    rw [Measure.map_smul _ (l.measurable_pointAt f i).aemeasurable,
      l.pointAt_observation_law f i hconst,
      Measure.map_smul _ (l.measurable_pointAt f i).aemeasurable] at hsegment
    rw [auxiliaryInterval, uniformLaw_restrict_interval hd ha (min_le_max) hb,
      Measure.map_smul _ (l.measurable_pointAt f i).aemeasurable,
      smul_smul, ← ENNReal.ofReal_mul hw, hc]
    exact hsegment.symm

end SegmentLottery
end Blotto
