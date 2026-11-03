import Blotto.GeneralPaperStoredCategoricalWork

/-! The actual Boolean-cache root selects its retained row list and runs
the verified scan in the same memory. Its price includes the root load and
all reached-row selection work; no source selector executes. -/
namespace Blotto.GeneralPaperStoredCacheCategoricalWork
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

def bound (model : RationalCostModel) (A w r count : ℕ) : ℕ :=
  GeneralPaperStoredCategoricalWork.bound model A w r count +
    GeneralPaperStoredReferenceReadWork.readBound model A A + 256 * (A + 1)

theorem work (model : RationalCostModel) (S A layoutStart start : ℕ) (plan : GeneralPaperMeasuredBlockPlan.Plan)
    (full : Directory A) (installed : Installed A) (ctx : Context model S A layoutStart plan full installed)
    (cache : GeneralPaperEqualBooleanCache.Cache prepared)
    (hRead : Readback model A installed (GeneralPaperBooleanRecordCursor.expected model S A cache start))
    (hHeaders : ∀ header ∈ (GeneralPaperBooleanRecordCursor.expected model S A cache start).headers,header ∈ full.headers)
    (hRoot : installed.root = (GeneralPaperBooleanRecordCursor.expected model S A cache start).root.reference)
    (word : FixedBinaryWord (prepared.rangeBits + 1)) :
    (GeneralPaperStoredBooleanCacheRead.categorical model A installed word.bits).2 ≤
      bound model A (prepared.rangeBits + 1) (GeneralPaperPositiveSegmentCompaction.count l) cache.rows.length := by
  obtain ⟨fieldStart,hLoad,_,hChildRead,hChildHeaders,_⟩ := GeneralPaperStoredChildRead.record_child model A start 64 installed
    (GeneralPaperBooleanRecordCursor.schema model S A cache) (GeneralPaperBooleanRecordCursor.child model S A cache)
    GeneralPaperBooleanRecordCursor.fields hRead hRoot ⟨1,by decide⟩
  let child := GeneralPaperBooleanRecordCursor.child model S A cache .rows fieldStart
  let loaded := GeneralPaperStoredScalarRead.atRoot installed child.root.reference
  have hScan := GeneralPaperStoredCategoricalWork.work model S A layoutStart fieldStart plan full loaded
    (GeneralPaperStoredReadContext.atRoot ctx child.root.reference) cache.rows hChildRead
    (fun header hh => hHeaders header (hChildHeaders header hh)) rfl word
  have hLoadWork := GeneralPaperStoredRecordReadWork.work model S A layoutStart start 64 plan full installed ctx
    (GeneralPaperBooleanRecordCursor.schema model S A cache) (GeneralPaperBooleanRecordCursor.child model S A cache)
    GeneralPaperBooleanRecordCursor.fields hRead hHeaders hRoot ⟨1,by decide⟩
  change (GeneralPaperStoredChildRead.load model A installed 0 1).1 = some (⟨A,loaded⟩ : Child) at hLoad
  change (GeneralPaperStoredChildRead.load model A installed 0 1).2 ≤ _ at hLoadWork
  rw [(GeneralPaperStoredBooleanCacheRead.categorical_trace model A installed loaded word.bits hLoad).2]
  unfold bound
  omega

end Blotto.GeneralPaperStoredCacheCategoricalWork
