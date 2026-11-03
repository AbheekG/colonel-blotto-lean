import Blotto.RationalThreeCodeBounds
import Blotto.PreparedSegmentDescriptor

/-! The counted code builds exactly the maintained native segment descriptor.
Its stored environment is shared by all weight and endpoint evaluations. -/

namespace Blotto

theorem RationalSegmentLottery.eq_of_fields {n k : ℕ} (a b : RationalSegmentLottery n k)
    (hw : a.weight = b.weight) (hP : a.P = b.P) (hQ : a.Q = b.Q) : a = b := by
  cases a
  cases b
  cases hw
  cases hP
  cases hQ
  rfl

namespace RationalThreeGeometryCode
open scoped BigOperators

def compiledLotteryReference (g : RationalThreeGeometry) : RationalSegmentLottery 3 9 :=
  let env := environment g
  { weight := fun slot => (chosen slot).value env
    P := fun slot j => (vertex (RationalThreeGeometry.edges slot).1 j).value env
    Q := fun slot j => (vertex (RationalThreeGeometry.edges slot).2 j).value env
    nonnegative := by intro slot; rw [chosen_value]; exact g.chosenWeights_nonnegative slot
    mass := by
      change (∑ slot, (chosen slot).value (environment g)) = 1
      simp only [chosen_value]
      exact g.chosenWeights_mass }

def compiledLottery (g : RationalThreeGeometry) : RationalSegmentLottery 3 9 :=
  (PreparedSegmentDescriptor.prepare (compiledLotteryReference g)).lottery

theorem compiledLottery_eq (g : RationalThreeGeometry) : compiledLottery g = g.segmentLottery := by
  rw [compiledLottery, PreparedSegmentDescriptor.lottery_eq]
  apply RationalSegmentLottery.eq_of_fields
  · funext slot; exact chosen_value g slot
  · funext slot j; exact vertex_value g _ j
  · funext slot j; exact vertex_value g _ j

theorem compiledLottery_real (g : RationalThreeGeometry) : (compiledLottery g).real = g.real.segmentLottery := by
  rw [compiledLottery_eq, g.segmentLottery_real]

end RationalThreeGeometryCode
end Blotto
