import Blotto.GeneralPaperNamedCircleBitPrice

/-! Read one retained prepared circle row and execute its complete bit
draw. No sort, coefficient, metadata or source preparation repeats. -/
namespace Blotto.GeneralPaperStoredCircleBitDraw
set_option autoImplicit false
set_option maxHeartbeats 3500000

def run {T n R : ℕ} (model : RationalCostModel) (A W S : ℕ) (state : GeneralPaperLightFieldScan.State n)
    (hR : 0<R) (c : ℚ) (prepared : FixedArrayTable T (GeneralPaperNamedCircleExecution.Prepared state R))
    (i : Fin T) (l : Fin S) : FixedArrayTable n ℚ×ℕ :=
  let output := GeneralPaperNamedCircleBitDraw.run model A W S state hR c (prepared.read i) l
  (output.1,output.2+64*A)

theorem data {T n R : ℕ} (model : RationalCostModel) (A W S : ℕ) (state : GeneralPaperLightFieldScan.State n)
    (hR : 0<R) (c : ℚ) (prepared : FixedArrayTable T (GeneralPaperNamedCircleExecution.Prepared state R))
    (i : Fin T) (l : Fin S) :
    (run model A W S state hR c prepared i l).1=
      (GeneralPaperStoredCirclePreparation.draw model W S state hR c prepared i l).1 :=
  GeneralPaperNamedCircleBitDraw.data model A W S state hR c (prepared.read i) l

def original {n T S : ℕ} (model : RationalCostModel) (A : ℕ) (o : GeneralPaperReducedValuesDriver.Output n)
    (hR : 0<o.representatives) (c : ℚ)
    (prepared : FixedArrayTable T (GeneralPaperNamedCircleExecution.Prepared o.classified o.representatives))
    (i : Fin T) (l : Fin S) : FixedArrayTable n ℚ×ℕ :=
  run model A o.classified.lightWeight S o.classified hR c prepared i l

theorem original_data {n T S : ℕ} (model : RationalCostModel) (A : ℕ) (o : GeneralPaperReducedValuesDriver.Output n)
    (hR : 0<o.representatives) (c : ℚ)
    (prepared : FixedArrayTable T (GeneralPaperNamedCircleExecution.Prepared o.classified o.representatives))
    (i : Fin T) (l : Fin S) :
    (original model A o hR c prepared i l).1=(GeneralPaperOriginalCirclePreparation.draw model o hR c prepared i l).1 :=
  data model A o.classified.lightWeight S o.classified hR c prepared i l

end Blotto.GeneralPaperStoredCircleBitDraw
