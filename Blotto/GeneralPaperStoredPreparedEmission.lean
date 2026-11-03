import Blotto.GeneralPaperStoredRouteEmission

/-! Actual prepared-root descent reaches the route array and emits the full
allocation from the materialized group array. Route count and labels are
loaded; source prepared data occur only in correspondence proofs. -/
namespace Blotto.GeneralPaperStoredPreparedEmission
open GeneralPaperFieldDirectory
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperSamplerRecordInstallation (Readback)
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
    let actual := GeneralPaperStoredRouteEmission.run model B loaded groups
    ⟨actual.values,actual.count,child.2 + actual.work + 64 * (A + B + 1)⟩

theorem trace (model : RationalCostModel) (A : ℕ) (installed loaded : Installed A) (groups : Array ℚ)
    (hChild : (GeneralPaperStoredChildRead.load model A installed 0 0).1 = some (⟨A,loaded⟩ : Child)) :
    (run model A installed groups).values = (GeneralPaperStoredRouteEmission.run model A loaded groups).values ∧
      (run model A installed groups).count = (GeneralPaperStoredRouteEmission.run model A loaded groups).count ∧
      (run model A installed groups).work = (GeneralPaperStoredChildRead.load model A installed 0 0).2 +
        (GeneralPaperStoredRouteEmission.run model A loaded groups).work + 128 * A + 64 := by
  simp only [run,hChild]
  refine ⟨True.intro,True.intro,?_⟩
  ring

theorem source (model : RationalCostModel) (S A start : ℕ) (installed : Installed A) (full : Directory A)
    (hContract : Contract model A installed full) (prepared : GeneralPaperEqualPreparedCache.Prepared G l)
    (hRead : Readback model A installed (GeneralPaperPreparedRecordCursor.expected model S A prepared start))
    (hHeaders : ∀ header ∈ (GeneralPaperPreparedRecordCursor.expected model S A prepared start).headers,header ∈ full.headers)
    (hRoot : installed.root = (GeneralPaperPreparedRecordCursor.expected model S A prepared start).root.reference)
    (groups : FixedArrayTable m ℚ) :
    ∃ root : FixedBinaryWord A,
      (run model A installed groups.data).values = some (prepared.routes.emit groups.read).data ∧
      (run model A installed groups.data).count = n ∧
      (run model A installed groups.data).work = (GeneralPaperStoredChildRead.load model A installed 0 0).2 +
        (GeneralPaperStoredRouteEmission.run model A (GeneralPaperStoredScalarRead.atRoot installed root) groups.data).work + 128 * A + 64 := by
  obtain ⟨fieldStart,hLoad,_,hChildRead,hChildHeaders,_⟩ := GeneralPaperStoredChildRead.record_child model A start 64 installed
    (GeneralPaperPreparedRecordCursor.schema model S A prepared) (GeneralPaperPreparedRecordCursor.child model S A prepared)
    GeneralPaperPreparedRecordCursor.fields hRead hRoot ⟨0,by decide⟩
  let child := GeneralPaperPreparedRecordCursor.child model S A prepared .routes fieldStart
  let loaded := GeneralPaperStoredScalarRead.atRoot installed child.root.reference
  have hChildContract : Contract model A loaded full := hContract
  obtain ⟨hv,hc,_⟩ := GeneralPaperStoredRouteEmission.source model S A fieldStart loaded full hChildContract prepared.routes.table
    hChildRead (fun header hh => hHeaders header (hChildHeaders header hh)) rfl groups
  have hTarget : (FixedArrayTable.ofFn (fun j => GeneralPaperStoredRouteCoordinate.value groups (prepared.routes.table.read j))).data =
      (prepared.routes.emit groups.read).data := by
    simp only [PreparedGroupOutput.emit,RationalProportionalGroups.emit,RationalResourceArray.ofAllocation,
      FixedArrayTable.read_ofFn,GeneralPaperStoredRouteCoordinate.value]
    rfl
  obtain ⟨hData,hCount,hWork⟩ := trace model A installed loaded groups.data hLoad
  exact ⟨child.root.reference,hData.trans (hv.trans (congrArg some hTarget)),hCount.trans hc,hWork⟩

end Blotto.GeneralPaperStoredPreparedEmission
