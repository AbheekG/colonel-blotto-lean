import Blotto.GeneralPaperStoredSamplerGroupsWork
import Blotto.GeneralPaperStoredEmissionWork
import Blotto.GeneralPaperStoredPostselection

/-! The complete actual postselection cost combines stored midpoint,
selected groups and every original-budget allocation coordinate. Its bound
is uniform over selected segment and fresh-bit block. -/
namespace Blotto.GeneralPaperStoredPostselectionWork
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperSamplerRecordInstallation (Readback)
open GeneralPaperFieldDirectory (Directory)
open GeneralPaperStoredReadContext (Context)
open GeneralPaperStoredChildRead (Child)
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
variable {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
open GeneralPaperPositiveSegmentCompaction (count)

def emissionHeight (s b c K : ℕ) : ℕ := max c (GeneralPaperEqualCachedEmission.scaledHeight s K b)

def bound (model : RationalCostModel) (A s b c : ℕ) (prepared : GeneralPaperEqualPreparedCache.Prepared G l) : ℕ :=
  GeneralPaperStoredSamplerGroupsWork.drawBound model A s b prepared +
    GeneralPaperStoredEmissionWork.samplerBound model A n m (emissionHeight s b c prepared.midpointBits) + 128 * (A + 1)

theorem work (model : RationalCostModel) (S A start s b c : ℕ) (installed : Installed A)
    (sampler : GeneralPaperEqualStoredBitSampler.Sampler G l)
    (ctx : Context model S A start (GeneralPaperEqualMeasuredRetainedPlan.sampler model S A sampler)
      (GeneralPaperSamplerRecordCursor.expected model S A sampler start) installed)
    (hRoot : installed.root = (GeneralPaperSamplerRecordCursor.expected model S A sampler start).root.reference)
    (hs : 2 ≤ s) (h : l.HeightAt s) (hB : RationalHeight sampler.prepared.budget b)
    (hc : 2 ≤ c) (hC : ∀ j,RationalHeight (sampler.prepared.routes.table.read j).2 c)
    (index : Fin (count l)) (fresh : Fin sampler.prepared.midpointBits → Bool) :
    (GeneralPaperStoredPostselection.run model A installed index.val GeneralPaperBooleanFreshWord.nextList (List.ofFn fresh)).work ≤
      bound model A s b c sampler.prepared := by
  have hGroups := GeneralPaperStoredSamplerGroupsWork.draw_work model S A start s b installed sampler ctx hRoot hs h hB index fresh
  have hEmission := GeneralPaperStoredEmissionWork.sampler_work model S A start (emissionHeight s b c sampler.prepared.midpointBits) installed sampler ctx hRoot
    (GeneralPaperEqualCachedEmission.scaledPoint sampler.prepared index fresh) (hc.trans (le_max_left _ _))
    (fun j => (hC j).mono (le_max_left _ _))
    (fun g => (GeneralPaperEqualCachedEmission.scaledPoint_height sampler.prepared hs h hB index fresh g).mono (le_max_right _ _))
  rw [(GeneralPaperStoredPostselection.source model S A start installed sampler ctx.contract hRoot index fresh).2.2.2]
  unfold bound
  omega

end Blotto.GeneralPaperStoredPostselectionWork
