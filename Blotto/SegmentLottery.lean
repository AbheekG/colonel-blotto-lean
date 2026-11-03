import Blotto.FiniteMixture
import Blotto.Boxes

/-! Explicit finite segment lotteries and affine scalar observations. -/

namespace Blotto
open MeasureTheory Set Filter
open scoped BigOperators

structure AffineProbe (n : ℕ) where
  value : Allocation n → ℝ
  measurable : Measurable value
  onSegment : ∀ P Q t, value (segmentPoint P Q t) = affineLine (value P) (value Q) t

namespace AffineProbe

noncomputable def coordinate {n : ℕ} (j : Fin n) : AffineProbe n :=
  ⟨(fun x => x j), measurable_pi_apply j, fun _ _ _ => rfl⟩

noncomputable def reflectedCoordinate {n : ℕ} (d : ℝ) (j : Fin n) : AffineProbe n where
  value := fun x => d - x j
  measurable := measurable_const.sub (measurable_pi_apply j)
  onSegment := by intro P Q t; dsimp [segmentPoint, affineLine]; ring

theorem map_segmentLaw {n : ℕ} (f : AffineProbe n) (P Q : Allocation n) :
    Measure.map f.value (segmentLaw P Q : Measure (Allocation n)) =
      (affineUniform (f.value P) (f.value Q) : Measure ℝ) := by
  change Measure.map f.value (Measure.map (segmentPoint P Q) (unitUniform : Measure ℝ)) =
    Measure.map (affineLine (f.value P) (f.value Q)) (unitUniform : Measure ℝ)
  rw [Measure.map_map f.measurable (measurable_segmentPoint P Q)]
  congr 1
  funext t
  exact f.onSegment P Q t

end AffineProbe

structure SegmentLottery (n k : ℕ) where
  weight : Fin k → ℝ
  P : Fin k → Allocation n
  Q : Fin k → Allocation n
  nonnegative : ∀ i, 0 ≤ weight i
  mass : ∑ i, weight i = 1

namespace SegmentLottery

noncomputable def law {n k : ℕ} (l : SegmentLottery n k) : Mixed n :=
  probabilityMixture l.weight (fun i => segmentLaw (l.P i) (l.Q i)) l.nonnegative l.mass

noncomputable def positiveSlots {n k : ℕ} (l : SegmentLottery n k) : Finset (Fin k) := by
  classical
  exact Finset.univ.filter fun i => 0 < l.weight i

noncomputable def point {n k : ℕ} (l : SegmentLottery n k) (i : Fin k) (t : ℝ) : Allocation n :=
  segmentPoint (l.P i) (l.Q i) t

theorem law_measure {n k : ℕ} (l : SegmentLottery n k) :
    (l.law : Measure (Allocation n)) =
      Measure.sum (fun i => ENNReal.ofReal (l.weight i) • (segmentLaw (l.P i) (l.Q i) : Measure (Allocation n))) := rfl

theorem probe_measure {n k : ℕ} (l : SegmentLottery n k) (f : AffineProbe n) :
    Measure.map f.value (l.law : Measure (Allocation n)) =
      Measure.sum (fun i => ENNReal.ofReal (l.weight i) •
        (affineUniform (f.value (l.P i)) (f.value (l.Q i)) : Measure ℝ)) := by
  change Measure.map f.value (mixtureMeasure l.weight (fun i => segmentLaw (l.P i) (l.Q i))) = _
  rw [mixtureMeasure_map _ _ _ f.measurable]
  congr 1
  funext i
  rw [f.map_segmentLaw]

theorem law_fullBudget {n k : ℕ} (l : SegmentLottery n k) {B : ℝ}
    (hP : ∀ i, FullBudget B (l.P i)) (hQ : ∀ i, FullBudget B (l.Q i)) :
    ∀ᵐ x ∂(l.law : Measure (Allocation n)), FullBudget B x := by
  apply probabilityMixture_ae
  intro i
  exact segmentLaw_fullBudget (hP i) (hQ i)

theorem point_fullBudget {n k : ℕ} (l : SegmentLottery n k) {B : ℝ}
    (hP : ∀ i, FullBudget B (l.P i)) (hQ : ∀ i, FullBudget B (l.Q i))
    (i : Fin k) {t : ℝ} (ht : 0 ≤ t ∧ t ≤ 1) : FullBudget B (l.point i t) :=
  segment_fullBudget (hP i) (hQ i) ht

/-- A continuous auxiliary marginal rules out positive mass on constant
auxiliary projections. This also covers degenerate parameter tables. -/
theorem constant_probe_weight_zero {n k : ℕ} (l : SegmentLottery n k) (f : AffineProbe n)
    (d : ℝ) (hm : Measure.map f.value (l.law : Measure (Allocation n)) = uniformLaw d)
    (i : Fin k) (hi : f.value (l.P i) = f.value (l.Q i)) : l.weight i = 0 := by
  have he := congrArg (fun μ : Measure ℝ => μ {f.value (l.P i)}) hm
  rw [l.probe_measure, Measure.sum_apply _ (measurableSet_singleton _), uniform_singleton] at he
  simp only [Measure.smul_apply, smul_eq_mul] at he
  have hl : ENNReal.ofReal (l.weight i) *
      (affineUniform (f.value (l.P i)) (f.value (l.Q i)) : Measure ℝ) {f.value (l.P i)} ≤
      ∑' j, ENNReal.ofReal (l.weight j) *
        (affineUniform (f.value (l.P j)) (f.value (l.Q j)) : Measure ℝ) {f.value (l.P i)} :=
    ENNReal.le_tsum (f := fun j => ENNReal.ofReal (l.weight j) *
      (affineUniform (f.value (l.P j)) (f.value (l.Q j)) : Measure ℝ) {f.value (l.P i)}) i
  rw [he, ← hi, affineUniform_constant] at hl
  have hl0 : ENNReal.ofReal (l.weight i) ≤ 0 := by simpa using hl
  have hz : ENNReal.ofReal (l.weight i) = 0 := le_antisymm hl0 zero_le
  exact le_antisymm (ENNReal.ofReal_eq_zero.mp hz) (l.nonnegative i)

end SegmentLottery
end Blotto
