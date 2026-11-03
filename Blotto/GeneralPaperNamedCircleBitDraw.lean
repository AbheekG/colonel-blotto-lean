import Blotto.GeneralPaperNativeChoiceArrayBits

/-! Complete native bit-draw data path: one priced selected-shift sweep,
one materialized choice array, native rational bids/name scatter and final
original-budget products. Every prepared object is retained and reused. -/
namespace Blotto.GeneralPaperNamedCircleBitDraw
open GeneralPaperNamedCircleExecution
set_option autoImplicit false
set_option maxHeartbeats 3500000

def run {n R : ℕ} (model : RationalCostModel) (A W S : ℕ) (state : GeneralPaperLightFieldScan.State n)
    (hR : 0<R) (c : ℚ) (prepared : Prepared state R) (l : Fin S) : FixedArrayTable n ℚ×ℕ :=
  let chosen := GeneralPaperNativeChoiceArrayBits.run model (fun w => w) A R W S l.val prepared.metadata
  let output := assemble model.rat (fun w => w) A state hR c prepared chosen.1
  (output.1,chosen.2+output.2+32*A)

theorem data {n R : ℕ} (model : RationalCostModel) (A W S : ℕ) (state : GeneralPaperLightFieldScan.State n)
    (hR : 0<R) (c : ℚ) (prepared : Prepared state R) (l : Fin S) :
    (run model A W S state hR c prepared l).1=(drawArithmetic model W S state hR c prepared l).1 := by
  dsimp only [run,drawArithmetic]
  rw [GeneralPaperNativeChoiceArrayBits.data]
  exact GeneralPaperNamedCircleHeight.assemble_models_data model.rat (fun _ => 1) (fun w => w) (fun _ => 1)
    A 1 state hR c prepared _

end Blotto.GeneralPaperNamedCircleBitDraw
