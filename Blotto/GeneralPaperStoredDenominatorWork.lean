import Blotto.GeneralPaperStoredRulerReadWork

/-! The Boolean-cache denominator follows one actual record child and
reconstructs only that retained word. Its enclosing context derives every
record/list capacity; neither source width nor denominator is a read input. -/
namespace Blotto.GeneralPaperStoredDenominatorWork
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperSamplerRecordInstallation (Readback)
open GeneralPaperFieldDirectory (Directory)
open GeneralPaperStoredReadContext (Context)
open GeneralPaperStoredChildRead (Child)
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 8192
variable {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
variable {prepared : GeneralPaperEqualPreparedCache.Prepared G l}

def bound (model : RationalCostModel) (A w : ℕ) : ℕ :=
  GeneralPaperStoredBooleanWordWork.bound model A w + GeneralPaperStoredReferenceReadWork.readBound model A A + 256 * (A + 1)

theorem work (model : RationalCostModel) (S A layoutStart start : ℕ) (plan : GeneralPaperMeasuredBlockPlan.Plan)
    (full : Directory A) (installed : Installed A) (ctx : Context model S A layoutStart plan full installed)
    (cache : GeneralPaperEqualBooleanCache.Cache prepared)
    (hRead : Readback model A installed (GeneralPaperBooleanRecordCursor.expected model S A cache start))
    (hHeaders : ∀ header ∈ (GeneralPaperBooleanRecordCursor.expected model S A cache start).headers,header ∈ full.headers)
    (hRoot : installed.root = (GeneralPaperBooleanRecordCursor.expected model S A cache start).root.reference) :
    (GeneralPaperStoredBooleanCacheRead.denominator model A installed).2 ≤ bound model A (prepared.rangeBits + 1) := by
  obtain ⟨fieldStart,hLoad,_,hChildRead,hChildHeaders,_⟩ := GeneralPaperStoredChildRead.record_child model A start 64 installed
    (GeneralPaperBooleanRecordCursor.schema model S A cache) (GeneralPaperBooleanRecordCursor.child model S A cache)
    GeneralPaperBooleanRecordCursor.fields hRead hRoot ⟨0,by decide⟩
  let child := GeneralPaperBooleanRecordCursor.child model S A cache .denominator fieldStart
  let loaded := GeneralPaperStoredScalarRead.atRoot installed child.root.reference
  have hWordWork := GeneralPaperStoredBooleanWordWork.work model S A layoutStart fieldStart plan full loaded
    (GeneralPaperStoredReadContext.atRoot ctx child.root.reference) cache.denominator hChildRead
    (fun header hh => hHeaders header (hChildHeaders header hh)) rfl
  have hLoadWork := GeneralPaperStoredRecordReadWork.work model S A layoutStart start 64 plan full installed ctx
    (GeneralPaperBooleanRecordCursor.schema model S A cache) (GeneralPaperBooleanRecordCursor.child model S A cache)
    GeneralPaperBooleanRecordCursor.fields hRead hHeaders hRoot ⟨0,by decide⟩
  change (GeneralPaperStoredChildRead.load model A installed 0 0).1 = some (⟨A,loaded⟩ : Child) at hLoad
  change (GeneralPaperStoredChildRead.load model A installed 0 0).2 ≤ _ at hLoadWork
  change (GeneralPaperStoredRecordCollectors.word model A installed 0).2 ≤ _
  rw [(GeneralPaperStoredRecordCollectors.word_trace model A installed loaded 0 hLoad).2]
  unfold bound
  omega

end Blotto.GeneralPaperStoredDenominatorWork
