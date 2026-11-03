import Blotto.RealThreeGeometryCompiler

/-! Ordered and swapped three-variable tables execute the counted geometry
formulas. The exceptional one-segment branch keeps its original safe rows. -/

namespace Blotto
open scoped Classical

namespace ThreeInput

noncomputable def compiledRealLottery (i : ThreeInput) : SegmentLottery 3 9 :=
  if he : 0 < i.a + i.d - i.B then RealThreeGeometryCode.compiledLottery (i.geometry he)
  else i.segmentLottery

theorem compiledRealLottery_eq (i : ThreeInput) : i.compiledRealLottery = i.segmentLottery := by
  unfold compiledRealLottery
  split_ifs with he
  · rw [RealThreeGeometryCode.compiledLottery_eq]
    simp only [segmentLottery, dite_eq_left he]
  · rfl

end ThreeInput
namespace ThreeSpec

noncomputable def compiledRealLottery (i : ThreeSpec) : SegmentLottery 3 9 :=
  if i.a ≤ i.d then i.orderedInput.compiledRealLottery
  else i.orderedInput.compiledRealLottery.mapped AffineAllocation.swapFirst

theorem compiledRealLottery_eq (i : ThreeSpec) : i.compiledRealLottery = i.segmentLottery := by
  unfold compiledRealLottery segmentLottery
  rw [i.orderedInput.compiledRealLottery_eq]

end ThreeSpec
end Blotto
