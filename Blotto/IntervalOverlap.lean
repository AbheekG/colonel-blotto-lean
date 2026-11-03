import Blotto.InverseSegment
import Blotto.LotteryDensity

/-! Exact overlap of two scalar segment supports. -/

namespace Blotto
open MeasureTheory Set

noncomputable def overlapLower (a b c d : ℝ) : ℝ := max (min a b) (min c d)
noncomputable def overlapUpper (a b c d : ℝ) : ℝ := min (max a b) (max c d)
noncomputable def overlapLength (a b c d : ℝ) : ℝ := max (overlapUpper a b c d - overlapLower a b c d) 0

theorem scalar_intervals_overlap (a b c d : ℝ) :
    Icc (min a b) (max a b) ∩ Icc (min c d) (max c d) =
      Icc (overlapLower a b c d) (overlapUpper a b c d) := by
  ext z
  simp only [mem_inter_iff, mem_Icc, overlapLower, overlapUpper, max_le_iff, le_min_iff]
  tauto

theorem rawInterval_overlap (a b c d : ℝ) :
    (rawInterval (min c d) (max c d)).restrict (Icc (min a b) (max a b)) =
      rawInterval (overlapLower a b c d) (overlapUpper a b c d) := by
  rw [rawInterval, Measure.restrict_restrict measurableSet_Icc, scalar_intervals_overlap]
  rfl

/-- Restricting one weighted observation gives exactly its constant density
on the common overlap, including empty and zero-length overlaps. -/
theorem weighted_observation_overlap (a b c d q : ℝ) (hq : 0 ≤ q) (hzero : c = d → q = 0) :
    ENNReal.ofReal q •
      (affineUniform c d : Measure ℝ).restrict (Icc (min a b) (max a b)) =
        ENNReal.ofReal (q / |d - c|) •
          rawInterval (overlapLower a b c d) (overlapUpper a b c d) := by
  have he := congrArg (fun μ : Measure ℝ => μ.restrict (Icc (min a b) (max a b)))
    (weighted_affine_sorted c d q hq hzero)
  rw [Measure.restrict_smul, Measure.restrict_smul, rawInterval_overlap] at he
  exact he

end Blotto
