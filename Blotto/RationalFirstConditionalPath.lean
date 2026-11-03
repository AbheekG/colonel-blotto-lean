import Blotto.RationalFirstConditional
import Blotto.NestedBoxes

/-! The native conditional descriptor's path equals the maintained real path
at every real scalar, including both endpoints. This transfers coordinate-box
guarantees without an almost-sure shortcut. -/

namespace Blotto.RationalNestedInput
open MeasureTheory Set

theorem firstConditionalLottery_path (i : RationalNestedInput) (htv : i.t ≤ i.v) (s : ℚ)
    (hs : 0 ≤ s ∧ s ≤ i.t) (slot : Fin 9) (u : ℝ) :
    segmentPoint ((i.firstConditionalLottery htv s hs).real.P slot)
      ((i.firstConditionalLottery htv s hs).real.Q slot) u =
      i.real.firstPoint (i.firstCase_real htv) s slot u := by
  have hsR := i.interval_real hs
  have he : 0 < i.conditionalProbability s ↔ 0 < i.real.conditionalProbability s := by
    rw [← i.conditionalProbability_real]
    norm_cast
  unfold firstConditionalLottery NestedInput.firstPoint
  by_cases hp : 0 < i.conditionalProbability s
  · rw [dite_eq_left hp, dite_eq_left (show (s : ℝ) ∈ i.real.positiveParameters from ⟨hsR, he.mp hp⟩),
      RationalSegmentLottery.shiftThird_real, RationalThreeGeometry.segmentLottery_real, i.firstGeometry_real]
    exact (AffineAllocation.shiftThird s).onSegment _ _ u |>.symm
  · have hn : (s : ℝ) ∉ i.real.positiveParameters := fun h => hp (he.mpr h.2)
    rw [dite_eq_right hp, dite_eq_right hn]
    funext j
    fin_cases j <;> simp [RationalSegmentLottery.real, segmentPoint, real]

theorem firstConditionalLottery_box (i : RationalNestedInput) (htv : i.t ≤ i.v) (s : ℚ)
    (hs : 0 ≤ s ∧ s ≤ i.t) (slot : Fin 9) :
    InBox ![(i.a : ℝ), (i.d : ℝ), (i.c : ℝ)] ((i.firstConditionalLottery htv s hs).real.P slot) ∧
      InBox ![(i.a : ℝ), (i.d : ℝ), (i.c : ℝ)] ((i.firstConditionalLottery htv s hs).real.Q slot) := by
  have hP := i.real.firstPoint_inBox (i.firstCase_real htv) (i.interval_real hs)
    (by norm_num : (0 : ℝ) ≤ 0 ∧ (0 : ℝ) ≤ 1) slot
  have hQ := i.real.firstPoint_inBox (i.firstCase_real htv) (i.interval_real hs)
    (by norm_num : (0 : ℝ) ≤ 1 ∧ (1 : ℝ) ≤ 1) slot
  rw [← i.firstConditionalLottery_path htv s hs slot 0] at hP
  rw [← i.firstConditionalLottery_path htv s hs slot 1] at hQ
  constructor
  · simpa only [InBox, segmentPoint, sub_zero, one_mul, zero_mul, add_zero, real] using hP
  · simpa only [InBox, segmentPoint, sub_self, zero_mul, one_mul, zero_add, real] using hQ

end Blotto.RationalNestedInput
