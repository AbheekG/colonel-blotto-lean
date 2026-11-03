import Blotto.SegmentLottery

/-! Invert a nonconstant affine scalar projection of a segment. -/

namespace Blotto
open MeasureTheory Set Filter

noncomputable def inverseParameter (a b z : ℝ) : ℝ := (z - a) / (b - a)

theorem inverseParameter_bounds {a b z : ℝ} (hab : a ≠ b)
    (hz : z ∈ Icc (min a b) (max a b)) :
    0 ≤ inverseParameter a b z ∧ inverseParameter a b z ≤ 1 := by
  rcases lt_or_gt_of_ne hab with h | h
  · have hd := sub_pos.mpr h
    have hz' : a ≤ z ∧ z ≤ b := by simpa [min_eq_left (le_of_lt h), max_eq_right (le_of_lt h)] using hz
    exact ⟨div_nonneg (sub_nonneg.mpr hz'.1) (le_of_lt hd), (div_le_one hd).mpr (by linarith [hz'.2])⟩
  · have hd := sub_pos.mpr h
    have hz' : b ≤ z ∧ z ≤ a := by simpa [min_eq_right (le_of_lt h), max_eq_left (le_of_lt h)] using hz
    have he : inverseParameter a b z = (a - z) / (a - b) := by
      dsimp [inverseParameter]
      field_simp [ne_of_gt hd, sub_ne_zero.mpr (Ne.symm hab)]
      ring
    rw [he]
    exact ⟨div_nonneg (sub_nonneg.mpr hz'.2) (le_of_lt hd), (div_le_one hd).mpr (by linarith [hz'.1])⟩

theorem affineLine_inverseParameter {a b : ℝ} (hab : a ≠ b) (z : ℝ) :
    affineLine a b (inverseParameter a b z) = z := by
  dsimp [affineLine, inverseParameter]
  field_simp [sub_ne_zero.mpr (Ne.symm hab)]
  ring

theorem inverseParameter_affineLine {a b : ℝ} (hab : a ≠ b) (t : ℝ) :
    inverseParameter a b (affineLine a b t) = t := by
  dsimp [inverseParameter, affineLine]
  field_simp [sub_ne_zero.mpr (Ne.symm hab)]
  ring

namespace SegmentLottery

noncomputable def pointAt {n k : ℕ} (l : SegmentLottery n k) (f : AffineProbe n)
    (i : Fin k) (z : ℝ) : Allocation n :=
  l.point i (inverseParameter (f.value (l.P i)) (f.value (l.Q i)) z)

theorem pointAt_probe {n k : ℕ} (l : SegmentLottery n k) (f : AffineProbe n) (i : Fin k)
    (hi : f.value (l.P i) ≠ f.value (l.Q i)) (z : ℝ) : f.value (l.pointAt f i z) = z := by
  rw [pointAt, point, f.onSegment, affineLine_inverseParameter hi]

theorem pointAt_fullBudget {n k : ℕ} (l : SegmentLottery n k) (f : AffineProbe n) {B : ℝ}
    (hP : ∀ i, FullBudget B (l.P i)) (hQ : ∀ i, FullBudget B (l.Q i)) (i : Fin k)
    (hi : f.value (l.P i) ≠ f.value (l.Q i)) {z : ℝ}
    (hz : z ∈ Icc (min (f.value (l.P i)) (f.value (l.Q i)))
      (max (f.value (l.P i)) (f.value (l.Q i)))) : FullBudget B (l.pointAt f i z) :=
  l.point_fullBudget hP hQ i (inverseParameter_bounds hi hz)

theorem measurable_pointAt {n k : ℕ} (l : SegmentLottery n k) (f : AffineProbe n) (i : Fin k) :
    Measurable (l.pointAt f i) := by
  exact (measurable_segmentPoint _ _).comp
    ((measurable_id.sub measurable_const).div_const _)

/-- Inverting the scalar projection recovers the original uniform segment law. -/
theorem pointAt_observation_law {n k : ℕ} (l : SegmentLottery n k) (f : AffineProbe n) (i : Fin k)
    (hi : f.value (l.P i) ≠ f.value (l.Q i)) :
    Measure.map (l.pointAt f i) (affineUniform (f.value (l.P i)) (f.value (l.Q i)) : Measure ℝ) =
      (segmentLaw (l.P i) (l.Q i) : Measure (Allocation n)) := by
  change Measure.map (l.pointAt f i)
    (Measure.map (affineLine (f.value (l.P i)) (f.value (l.Q i))) (unitUniform : Measure ℝ)) =
      Measure.map (segmentPoint (l.P i) (l.Q i)) (unitUniform : Measure ℝ)
  rw [Measure.map_map (l.measurable_pointAt f i) (measurable_affineLine _ _)]
  congr 1
  funext t
  dsimp [Function.comp_def, pointAt, point]
  rw [inverseParameter_affineLine hi]

theorem pointAt_inverse_segment {n k : ℕ} (l : SegmentLottery n k) (f : AffineProbe n) (i : Fin k)
    (hi : f.value (l.P i) ≠ f.value (l.Q i)) (t : ℝ) :
    l.pointAt f i (f.value (segmentPoint (l.P i) (l.Q i) t)) = segmentPoint (l.P i) (l.Q i) t := by
  rw [pointAt, point, f.onSegment, inverseParameter_affineLine hi]

theorem pointAt_inverse_ae {n k : ℕ} (l : SegmentLottery n k) (f : AffineProbe n) (i : Fin k)
    (hi : f.value (l.P i) ≠ f.value (l.Q i)) :
    ∀ᵐ x ∂(segmentLaw (l.P i) (l.Q i) : Measure (Allocation n)), l.pointAt f i (f.value x) = x := by
  have hp : MeasurableSet {x : Allocation n | l.pointAt f i (f.value x) = x} :=
    measurableSet_eq_fun ((l.measurable_pointAt f i).comp f.measurable) measurable_id
  change ∀ᵐ x ∂Measure.map (segmentPoint (l.P i) (l.Q i)) (unitUniform : Measure ℝ), l.pointAt f i (f.value x) = x
  rw [ae_map_iff (measurable_segmentPoint _ _).aemeasurable hp]
  exact Eventually.of_forall (l.pointAt_inverse_segment f i hi)

/-- A restricted segment observation determines its entire allocation. -/
theorem lift_observation_restrict {n k : ℕ} {β : Type*} [MeasurableSpace β]
    (l : SegmentLottery n k) (f : AffineProbe n) (i : Fin k)
    (hi : f.value (l.P i) ≠ f.value (l.Q i)) (H : Allocation n → β) (hH : Measurable H)
    (S : Set ℝ) (hS : MeasurableSet S) :
    Measure.map H ((segmentLaw (l.P i) (l.Q i) : Measure (Allocation n)).restrict (f.value ⁻¹' S)) =
      Measure.map (H ∘ l.pointAt f i)
        ((affineUniform (f.value (l.P i)) (f.value (l.Q i)) : Measure ℝ).restrict S) := by
  rw [← f.map_segmentLaw, Measure.restrict_map f.measurable hS,
    Measure.map_map (hH.comp (l.measurable_pointAt f i)) f.measurable]
  apply Measure.map_congr
  have he := ae_restrict_of_ae (s := f.value ⁻¹' S) (l.pointAt_inverse_ae f i hi)
  exact he.mono fun x hx => congrArg H hx.symm

end SegmentLottery
end Blotto
