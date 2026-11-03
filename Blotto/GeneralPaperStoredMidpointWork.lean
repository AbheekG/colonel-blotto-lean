import Blotto.GeneralPaperStoredPreparedReadWork
import Blotto.GeneralPaperStoredFreshDecoderWork
import Blotto.GeneralPaperStoredMidpointRead

/-! The complete actual prepared-root midpoint price joins control reads,
fresh collection, balanced decoding and rational assembly. Measured scalar
owners derive the decoder capacity; it is not a caller-supplied fit oracle. -/
namespace Blotto.GeneralPaperStoredMidpointWork
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperSamplerRecordInstallation (Readback)
open GeneralPaperFieldDirectory (Directory)
open GeneralPaperStoredReadContext (Context)
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8192
variable {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}

def bound (model : RationalCostModel) (A : ℕ) (prepared : GeneralPaperEqualPreparedCache.Prepared G l) : ℕ :=
  GeneralPaperStoredPreparedReadWork.controlsBound model A prepared +
    GeneralPaperStoredFreshDecoderWork.bound model A prepared.midpointBits +
    24 * model.rat (1 + 2 * GeneralPaperCachedMidpointAssembly.height prepared.midpointBits) +
    96 * A + 96 + 128 * (A + 1)

theorem work (model : RationalCostModel) (S A layoutStart start : ℕ) (plan : GeneralPaperMeasuredBlockPlan.Plan)
    (full : Directory A) (installed : Installed A) (ctx : Context model S A layoutStart plan full installed)
    (prepared : GeneralPaperEqualPreparedCache.Prepared G l)
    (hRead : Readback model A installed (GeneralPaperPreparedRecordCursor.expected model S A prepared start))
    (hHeaders : ∀ header ∈ (GeneralPaperPreparedRecordCursor.expected model S A prepared start).headers,header ∈ full.headers)
    (hCells : ∀ cell ∈ (GeneralPaperPreparedRecordCursor.expected model S A prepared start).cells,cell ∈ full.cells)
    (hRoot : installed.root = (GeneralPaperPreparedRecordCursor.expected model S A prepared start).root.reference)
    (fresh : Fin prepared.midpointBits → Bool) :
    (GeneralPaperStoredMidpointRead.run model A installed GeneralPaperBooleanFreshWord.nextList (List.ofFn fresh)).work ≤
      bound model A prepared := by
  have hControls := GeneralPaperStoredPreparedReadWork.controls_work model S A layoutStart start plan full installed ctx prepared hRead hHeaders hRoot
  have hCapacity := GeneralPaperStoredPreparedReadWork.midpoint_capacity model S A layoutStart start plan full installed ctx prepared hRead hCells hRoot
  have hFresh := GeneralPaperStoredFreshDecoderWork.work model A prepared.midpointBits GeneralPaperBooleanFreshWord.nextList (List.ofFn fresh) ctx.positive hCapacity
  have hAssembly := GeneralPaperStoredMidpointAssembly.work prepared model A (balancedBitIndex prepared.midpointBits fresh).val
    (balancedBitIndex prepared.midpointBits fresh).isLt
  rw [(GeneralPaperStoredMidpointRead.source model S A start installed full ctx.contract prepared hRead hHeaders hRoot fresh).2.2.2]
  unfold bound
  omega

end Blotto.GeneralPaperStoredMidpointWork
