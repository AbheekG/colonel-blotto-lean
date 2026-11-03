import Blotto.GeneralPaperStoredPreparedEmission

/-! Load the sampler's actual prepared child, then emit through its actual
route array. Every output word and the complete local read/copy/control work
are produced from the same retained memory and the supplied group array. -/
namespace Blotto.GeneralPaperStoredSamplerEmission
open GeneralPaperFieldDirectory
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperHeaderCountInstallation (Contract)
open GeneralPaperStoredChildRead (Child)
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 8192
variable {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}

def run (model : RationalCostModel) (A : ℕ) (installed : Installed A) (groups : Array ℚ) : GeneralPaperStoredRouteEmission.Result :=
  let child := GeneralPaperStoredChildRead.load model A installed 0 0
  match child.1 with
  | none => ⟨none,0,child.2 + 64 * (A + 1)⟩
  | some ⟨B,loaded⟩ =>
    let actual := GeneralPaperStoredPreparedEmission.run model B loaded groups
    ⟨actual.values,actual.count,child.2 + actual.work + 64 * (A + B + 1)⟩

theorem trace (model : RationalCostModel) (A : ℕ) (installed loaded : Installed A) (groups : Array ℚ)
    (hChild : (GeneralPaperStoredChildRead.load model A installed 0 0).1 = some (⟨A,loaded⟩ : Child)) :
    (run model A installed groups).values = (GeneralPaperStoredPreparedEmission.run model A loaded groups).values ∧
      (run model A installed groups).count = (GeneralPaperStoredPreparedEmission.run model A loaded groups).count ∧
      (run model A installed groups).work = (GeneralPaperStoredChildRead.load model A installed 0 0).2 +
        (GeneralPaperStoredPreparedEmission.run model A loaded groups).work + 128 * A + 64 := by
  simp only [run,hChild]
  refine ⟨True.intro,True.intro,?_⟩
  ring

theorem source (model : RationalCostModel) (S A start : ℕ) (installed : Installed A)
    (sampler : GeneralPaperEqualStoredBitSampler.Sampler G l)
    (hContract : Contract model A installed (GeneralPaperSamplerRecordCursor.expected model S A sampler start))
    (hRoot : installed.root = (GeneralPaperSamplerRecordCursor.expected model S A sampler start).root.reference)
    (groups : FixedArrayTable m ℚ) :
    ∃ root : FixedBinaryWord A,
      (run model A installed groups.data).values = some (sampler.prepared.routes.emit groups.read).data ∧
      (run model A installed groups.data).count = n ∧
      (run model A installed groups.data).work = (GeneralPaperStoredChildRead.load model A installed 0 0).2 +
        (GeneralPaperStoredPreparedEmission.run model A (GeneralPaperStoredScalarRead.atRoot installed root) groups.data).work + 128 * A + 64 := by
  obtain ⟨fieldStart,hLoad,_,hRead,hHeaders,_⟩ := GeneralPaperStoredChildRead.record_child model A start 64 installed
    (GeneralPaperSamplerRecordCursor.schema model S A sampler) (GeneralPaperSamplerRecordCursor.child model S A sampler)
    GeneralPaperSamplerRecordCursor.fields hContract.2.1 hRoot ⟨0,by decide⟩
  let child := GeneralPaperSamplerRecordCursor.child model S A sampler .prepared fieldStart
  let loaded := GeneralPaperStoredScalarRead.atRoot installed child.root.reference
  have hChildContract : Contract model A loaded (GeneralPaperSamplerRecordCursor.expected model S A sampler start) := hContract
  obtain ⟨_,hv,hc,_⟩ := GeneralPaperStoredPreparedEmission.source model S A fieldStart loaded _ hChildContract sampler.prepared hRead hHeaders rfl groups
  obtain ⟨hData,hCount,hWork⟩ := trace model A installed loaded groups.data hLoad
  exact ⟨child.root.reference,hData.trans hv,hCount.trans hc,hWork⟩

end Blotto.GeneralPaperStoredSamplerEmission
