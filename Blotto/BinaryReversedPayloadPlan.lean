import Blotto.BinaryUnaryPayloadPlan

/-! The positive accuracy reader consumes the reached reversed payload plan,
without constructing an unused forward reversal or an old reader replay. -/
namespace Blotto.BinaryReversedPayloadPlan
open BinarySeedPreparationSpace BinaryTracePlanMeasured
open BinaryNumericalReadbackPlan (finish view)
set_option autoImplicit false

def read (frame : List Bool) := finish (BinaryUnaryPayloadPlan.readReversedAt frame 0)

theorem read_compat (frame : List Bool) : (read frame).1 = BinaryUnaryPayloadMeasured.readReversed frame :=
  BinaryNumericalReadbackPlan.finish_compat (BinaryUnaryPayloadPlan.readReversed_refines frame 0)

theorem read_price (frame : List Bool) : (read frame).2 ≤ 30*(read frame).1.2 := by
  have hb := BinaryUnaryPayloadPlan.readReversed_budget frame 0
  have he := BinaryNumericalReadbackPlan.finish_bound (BinaryUnaryPayloadPlan.readReversedAt frame 0) hb.1
  have hw : 4 ≤ (BinaryUnaryPayloadPlan.readReversedAt frame 0).2 := by
    unfold BinaryUnaryPayloadPlan.readReversedAt
    dsimp only
    split <;> dsimp only <;> omega
  simp only [read,BinaryNumericalReadbackPlan.finish_record,view,denote_length] at he ⊢
  omega

end Blotto.BinaryReversedPayloadPlan
