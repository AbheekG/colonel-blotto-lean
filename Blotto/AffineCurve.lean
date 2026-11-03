import Blotto.IntervalOverlap
import Blotto.GluingBudget

/-! Affine output curves and their weighted interval laws. -/

namespace Blotto
open MeasureTheory Set

structure AffineCurve (n : ℕ) where
  value : ℝ → Allocation n
  measurable : Measurable value
  onInterval : ∀ a b t, value (affineLine a b t) = segmentPoint (value a) (value b) t

namespace AffineCurve

theorem map_affineUniform {n : ℕ} (C : AffineCurve n) (a b : ℝ) :
    Measure.map C.value (affineUniform a b : Measure ℝ) =
      (segmentLaw (C.value a) (C.value b) : Measure (Allocation n)) := by
  change Measure.map C.value (Measure.map (affineLine a b) (unitUniform : Measure ℝ)) =
    Measure.map (segmentPoint (C.value a) (C.value b)) (unitUniform : Measure ℝ)
  rw [Measure.map_map C.measurable (measurable_affineLine a b)]
  congr 1
  funext t
  exact C.onInterval a b t

/-- Empty and zero-length overlaps contribute zero mass. -/
theorem weighted_interval {n : ℕ} (C : AffineCurve n) (a b r : ℝ) (hr : 0 ≤ r) :
    ENNReal.ofReal (r * max (b - a) 0) • (segmentLaw (C.value a) (C.value b) : Measure (Allocation n)) =
      ENNReal.ofReal r • Measure.map C.value (rawInterval a b) := by
  by_cases hab : a ≤ b
  · have he := congrArg (Measure.map C.value) (weighted_affine_interval hab hr)
    rw [Measure.map_smul _ C.measurable.aemeasurable, C.map_affineUniform,
      Measure.map_smul _ C.measurable.aemeasurable] at he
    rw [max_eq_left (sub_nonneg.mpr hab), mul_comm r]
    exact he
  · have hba := lt_of_not_ge hab
    have hi : Icc a b = ∅ := Icc_eq_empty_of_lt hba
    simp [rawInterval, hi, max_eq_right (le_of_lt (sub_neg.mpr hba))]

end AffineCurve

namespace SegmentLottery

noncomputable def inverseCurve {n k : ℕ} (l : SegmentLottery n k) (f : AffineProbe n) (i : Fin k) : AffineCurve n where
  value := l.pointAt f i
  measurable := l.measurable_pointAt f i
  onInterval := by
    intro a b t
    funext j
    dsimp [pointAt, point, segmentPoint, inverseParameter, affineLine]
    ring

end SegmentLottery

/-- Two inverted source segments produce one affine four-coordinate curve
on their common auxiliary interval. -/
noncomputable def pairGlueCurve {k h : ℕ} (A : SegmentLottery 3 k) (B : SegmentLottery 3 h)
    (f g : AffineProbe 3) (i : Fin k) (j : Fin h) : AffineCurve 4 where
  value := fun z => glueAllocation (A.pointAt f i z, B.pointAt g j z)
  measurable := measurable_glueAllocation.comp
    ((A.measurable_pointAt f i).prodMk (B.measurable_pointAt g j))
  onInterval := by
    intro a b t
    have hA := (A.inverseCurve f i).onInterval a b t
    have hB := (B.inverseCurve g j).onInterval a b t
    funext r
    fin_cases r
    · exact congrArg (fun x : Allocation 3 => x 0) hA
    · exact congrArg (fun x : Allocation 3 => x 1) hA
    · exact congrArg (fun x : Allocation 3 => x 1) hB
    · exact congrArg (fun x : Allocation 3 => x 2) hB

end Blotto
