import Blotto.GeneralPaperStoredPreparedGroupsWork
import Blotto.GeneralPaperStoredSamplerMidpointWork
import Blotto.GeneralPaperStoredSamplerGroups

/-! Actual sampler-root group production includes the loaded midpoint and
one selected endpoint/interpolation pass, with each entry charged once. -/
namespace Blotto.GeneralPaperStoredSamplerGroupsWork
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

def runBound (model : RationalCostModel) (A m s b K : ℕ) : ℕ :=
  GeneralPaperStoredPreparedGroupsWork.bound model A m s b K +
    GeneralPaperStoredReferenceReadWork.readBound model A A + 256 * (A + 1)

def drawBound (model : RationalCostModel) (A s b : ℕ) (prepared : GeneralPaperEqualPreparedCache.Prepared G l) : ℕ :=
  GeneralPaperStoredSamplerMidpointWork.bound model A prepared + runBound model A m s b prepared.midpointBits + 128 * (A + 1)

theorem run_work (model : RationalCostModel) (S A start s b : ℕ) (installed : Installed A)
    (sampler : GeneralPaperEqualStoredBitSampler.Sampler G l)
    (ctx : Context model S A start (GeneralPaperEqualMeasuredRetainedPlan.sampler model S A sampler)
      (GeneralPaperSamplerRecordCursor.expected model S A sampler start) installed)
    (hRoot : installed.root = (GeneralPaperSamplerRecordCursor.expected model S A sampler start).root.reference)
    (hs : 2 ≤ s) (h : l.HeightAt s) (hB : RationalHeight sampler.prepared.budget b)
    (index : Fin (count l)) (fresh : Fin sampler.prepared.midpointBits → Bool) :
    (GeneralPaperStoredSamplerGroups.run model A installed index.val (GeneralPaperEqualPreparedCache.midpoint sampler.prepared fresh)).2 ≤
      runBound model A m s b sampler.prepared.midpointBits := by
  obtain ⟨fieldStart,hLoad,_,hRead,hHeaders,_⟩ := GeneralPaperStoredChildRead.record_child model A start 64 installed
    (GeneralPaperSamplerRecordCursor.schema model S A sampler) (GeneralPaperSamplerRecordCursor.child model S A sampler)
    GeneralPaperSamplerRecordCursor.fields ctx.contract.2.1 hRoot ⟨0,by decide⟩
  let child := GeneralPaperSamplerRecordCursor.child model S A sampler .prepared fieldStart
  let loaded := GeneralPaperStoredScalarRead.atRoot installed child.root.reference
  have hGroups := GeneralPaperStoredPreparedGroupsWork.work model S A start fieldStart s b _ _ loaded
    (GeneralPaperStoredReadContext.atRoot ctx child.root.reference) sampler.prepared hRead hHeaders rfl hs h hB index fresh
  have hLoadWork := GeneralPaperStoredRecordReadWork.work model S A start start 64 _ _ installed ctx
    (GeneralPaperSamplerRecordCursor.schema model S A sampler) (GeneralPaperSamplerRecordCursor.child model S A sampler)
    GeneralPaperSamplerRecordCursor.fields ctx.contract.2.1 (fun _ hh => hh) hRoot ⟨0,by decide⟩
  change (GeneralPaperStoredChildRead.load model A installed 0 0).1 = some (⟨A,loaded⟩ : Child) at hLoad
  change (GeneralPaperStoredChildRead.load model A installed 0 0).2 ≤ _ at hLoadWork
  rw [(GeneralPaperStoredSamplerGroups.trace model A installed loaded index.val (GeneralPaperEqualPreparedCache.midpoint sampler.prepared fresh) hLoad).2]
  unfold runBound
  omega

theorem draw_work (model : RationalCostModel) (S A start s b : ℕ) (installed : Installed A)
    (sampler : GeneralPaperEqualStoredBitSampler.Sampler G l)
    (ctx : Context model S A start (GeneralPaperEqualMeasuredRetainedPlan.sampler model S A sampler)
      (GeneralPaperSamplerRecordCursor.expected model S A sampler start) installed)
    (hRoot : installed.root = (GeneralPaperSamplerRecordCursor.expected model S A sampler start).root.reference)
    (hs : 2 ≤ s) (h : l.HeightAt s) (hB : RationalHeight sampler.prepared.budget b)
    (index : Fin (count l)) (fresh : Fin sampler.prepared.midpointBits → Bool) :
    (GeneralPaperStoredSamplerGroups.draw model A installed index.val GeneralPaperBooleanFreshWord.nextList (List.ofFn fresh)).work ≤
      drawBound model A s b sampler.prepared := by
  have hMidpoint := GeneralPaperStoredSamplerMidpointWork.work model S A start installed sampler ctx hRoot fresh
  have hGroups := run_work model S A start s b installed sampler ctx hRoot hs h hB index fresh
  rw [(GeneralPaperStoredSamplerGroups.draw_source model S A start installed sampler ctx.contract hRoot index fresh).2.2.2]
  unfold drawBound
  omega

end Blotto.GeneralPaperStoredSamplerGroupsWork
