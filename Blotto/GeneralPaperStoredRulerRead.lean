import Blotto.GeneralPaperStoredSamplerBooleanRead

/-! The Boolean cache's ruler count is loaded through its actual child
reference. Its representability follows from the actual global owner extent,
not from an execution length or capacity certificate. -/
namespace Blotto.GeneralPaperStoredRulerRead
open GeneralPaperFieldDirectory GeneralPaperReferenceRegionSlots
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperSamplerRecordInstallation (Readback)
open GeneralPaperHeaderCountInstallation (Contract)
open GeneralPaperStoredChildRead (Child)
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 8192
variable {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
variable {prepared : GeneralPaperEqualPreparedCache.Prepared G l}

def read (model : RationalCostModel) (A : ℕ) (installed : Installed A) : Option ℕ × ℕ :=
  let child := GeneralPaperStoredChildRead.load model A installed 0 2
  match child.1 with
  | none => (none,child.2 + 64 * (A + 1))
  | some ⟨B,loaded⟩ =>
    let actual := GeneralPaperRulerFieldCursor.read model B loaded
    (actual.1,child.2 + actual.2 + 64 * (A + B + 1))

theorem trace (model : RationalCostModel) (A : ℕ) (installed loaded : Installed A)
    (hChild : (GeneralPaperStoredChildRead.load model A installed 0 2).1 = some (⟨A,loaded⟩ : Child)) :
    (read model A installed).1 = (GeneralPaperRulerFieldCursor.read model A loaded).1 ∧
      (read model A installed).2 = (GeneralPaperStoredChildRead.load model A installed 0 2).2 +
        (GeneralPaperRulerFieldCursor.read model A loaded).2 + 128 * A + 64 := by
  simp only [read,hChild]
  constructor
  · exact True.intro
  · ring

theorem source (model : RationalCostModel) (S A layoutStart start : ℕ) (installed : Installed A)
    (full : Directory A) (plan : GeneralPaperMeasuredBlockPlan.Plan) (hContract : Contract model A installed full)
    (hSafe : GeneralPaperFieldDirectorySafety.Safe (GeneralPaperMeasuredBlockLayout.run model S A layoutStart plan).1 full)
    (hA : 0 < A) (hCap : layoutStart + plan.sizes.sum < 2 ^ A) (cache : GeneralPaperEqualBooleanCache.Cache prepared)
    (hRead : Readback model A installed (GeneralPaperBooleanRecordCursor.expected model S A cache start))
    (hHeaders : ∀ header ∈ (GeneralPaperBooleanRecordCursor.expected model S A cache start).headers,header ∈ full.headers)
    (hRoot : installed.root = (GeneralPaperBooleanRecordCursor.expected model S A cache start).root.reference) :
    ∃ root : FixedBinaryWord A,
      (read model A installed).1 = some prepared.rangeBits ∧
      (read model A installed).2 = (GeneralPaperStoredChildRead.load model A installed 0 2).2 +
        (GeneralPaperRulerFieldCursor.read model A (GeneralPaperStoredScalarRead.atRoot installed root)).2 + 128 * A + 64 := by
  obtain ⟨fieldStart,hLoad,_,_,hChildHeaders,_⟩ := GeneralPaperStoredChildRead.record_child model A start 64 installed
    (GeneralPaperBooleanRecordCursor.schema model S A cache) (GeneralPaperBooleanRecordCursor.child model S A cache)
    GeneralPaperBooleanRecordCursor.fields hRead hRoot ⟨2,by decide⟩
  let child := GeneralPaperBooleanRecordCursor.child model S A cache .ruler fieldStart
  have hHeader : (⟨(GeneralPaperRulerFieldCursor.expected A fieldStart cache.ruler).root,0,
      [FixedBinaryWord.ofNat A cache.ruler.length]⟩ : Header A) ∈ full.headers :=
    hHeaders _ (hChildHeaders _ (List.mem_singleton_self _))
  have hCount := GeneralPaperRetainedHeaderCountSources.ruler model S A layoutStart fieldStart plan installed full hContract
    hSafe hA hCap cache.ruler hHeader
  obtain ⟨hv,hw⟩ := trace model A installed (GeneralPaperStoredScalarRead.atRoot installed child.root.reference) hLoad
  exact ⟨child.root.reference,hv.trans (hCount.trans (congrArg some cache.ruler_length)),hw⟩

end Blotto.GeneralPaperStoredRulerRead
