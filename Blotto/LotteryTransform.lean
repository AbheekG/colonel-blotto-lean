import Blotto.SegmentLottery
import Blotto.Permutation

/-! Affine coordinate transformations of finite segment descriptions. -/

namespace Blotto
open MeasureTheory Set

structure AffineAllocation (n m : ℕ) where
  value : Allocation n → Allocation m
  measurable : Measurable value
  onSegment : ∀ P Q t, value (segmentPoint P Q t) = segmentPoint (value P) (value Q) t

namespace AffineAllocation

noncomputable def swapFirst : AffineAllocation 3 3 where
  value := Blotto.swapFirst
  measurable := measurable_swapFirst
  onSegment := by intro P Q t; funext j; fin_cases j <;> rfl

theorem map_segmentLaw {n m : ℕ} (f : AffineAllocation n m) (P Q : Allocation n) :
    Measure.map f.value (segmentLaw P Q : Measure (Allocation n)) =
      (segmentLaw (f.value P) (f.value Q) : Measure (Allocation m)) := by
  change Measure.map f.value (Measure.map (segmentPoint P Q) (unitUniform : Measure ℝ)) =
    Measure.map (segmentPoint (f.value P) (f.value Q)) (unitUniform : Measure ℝ)
  rw [Measure.map_map f.measurable (measurable_segmentPoint P Q)]
  congr 1
  funext t
  exact f.onSegment P Q t

end AffineAllocation

namespace SegmentLottery

noncomputable def mapped {n m k : ℕ} (l : SegmentLottery n k) (f : AffineAllocation n m) : SegmentLottery m k :=
  ⟨l.weight, (fun i => f.value (l.P i)), (fun i => f.value (l.Q i)), l.nonnegative, l.mass⟩

theorem mapped_law {n m k : ℕ} (l : SegmentLottery n k) (f : AffineAllocation n m) :
    ((l.mapped f).law : Measure (Allocation m)) = Measure.map f.value (l.law : Measure (Allocation n)) := by
  change mixtureMeasure l.weight (fun i => segmentLaw (f.value (l.P i)) (f.value (l.Q i))) =
    Measure.map f.value (mixtureMeasure l.weight (fun i => segmentLaw (l.P i) (l.Q i)))
  rw [mixtureMeasure_map _ _ _ f.measurable]
  unfold mixtureMeasure
  congr 1
  funext i
  rw [f.map_segmentLaw]

theorem mapped_positiveSlots {n m k : ℕ} (l : SegmentLottery n k) (f : AffineAllocation n m) :
    (l.mapped f).positiveSlots = l.positiveSlots := rfl

end SegmentLottery
end Blotto
