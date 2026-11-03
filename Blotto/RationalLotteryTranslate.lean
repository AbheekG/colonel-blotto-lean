import Blotto.RationalSegmentLottery
import Blotto.LotteryTransform
import Blotto.Translate

/-! A native third-coordinate translation of a rational descriptor. Its
weights are unchanged, and both the exact law and every segment path commute
with the maintained real translation. -/

namespace Blotto
open MeasureTheory

noncomputable def AffineAllocation.shiftThird (s : ℝ) : AffineAllocation 3 3 where
  value := Blotto.shiftThird s
  measurable := measurable_shiftThird s
  onSegment := by
    intro P Q t
    funext j
    fin_cases j
    · rfl
    · rfl
    · dsimp [Blotto.shiftThird, segmentPoint]
      ring

namespace RationalSegmentLottery

def shiftThird {k : ℕ} (l : RationalSegmentLottery 3 k) (s : ℚ) : RationalSegmentLottery 3 k :=
  ⟨l.weight, (fun slot => ![l.P slot 0, l.P slot 1, l.P slot 2 + s]),
    (fun slot => ![l.Q slot 0, l.Q slot 1, l.Q slot 2 + s]), l.nonnegative, l.mass⟩

theorem shiftThird_real {k : ℕ} (l : RationalSegmentLottery 3 k) (s : ℚ) :
    (l.shiftThird s).real = l.real.mapped (AffineAllocation.shiftThird s) := by
  apply SegmentLottery.eq_of_fields
  · rfl
  · funext slot j
    fin_cases j <;> simp [shiftThird, real, SegmentLottery.mapped, AffineAllocation.shiftThird, Blotto.shiftThird]
  · funext slot j
    fin_cases j <;> simp [shiftThird, real, SegmentLottery.mapped, AffineAllocation.shiftThird, Blotto.shiftThird]

theorem shiftThird_law {k : ℕ} (l : RationalSegmentLottery 3 k) (s : ℚ) :
    (l.shiftThird s).real.law = shiftedLaw s l.real.law := by
  rw [l.shiftThird_real]
  apply ProbabilityMeasure.toMeasure_injective
  exact l.real.mapped_law (AffineAllocation.shiftThird s)

theorem shiftThird_point_real {k : ℕ} (l : RationalSegmentLottery 3 k) (s : ℚ) (K : ℕ)
    (slot : Fin k) (bits : Fin K → Bool) :
    (fun j => ((l.shiftThird s).point K slot bits j : ℝ)) =
      Blotto.shiftThird s (l.real.dyadicPoint K slot bits) := by
  rw [point_real, l.shiftThird_real]
  exact (AffineAllocation.shiftThird s).onSegment (l.real.P slot) (l.real.Q slot) (dyadicMidpointSample K bits) |>.symm

end RationalSegmentLottery
end Blotto
