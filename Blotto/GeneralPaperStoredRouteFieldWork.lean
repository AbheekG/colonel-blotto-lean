import Blotto.GeneralPaperStoredPreparedGroupsWork
import Blotto.GeneralPaperStoredRouteReadback

/-! Actual route decoding prices its presence bit, optional label and
coefficient at their own encoded widths in the enclosing retained memory. -/
namespace Blotto.GeneralPaperStoredRouteFieldWork
open GeneralPaperFieldDirectory GeneralPaperReferenceRegionSlots GeneralPaperRetainedScalarValue
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperSamplerRecordInstallation (Readback)
open GeneralPaperStoredReadContext (Context)
open GeneralPaperUnifiedFieldValue (referenceMemory)
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192

def bound (model : RationalCostModel) (A m : ℕ) (coefficient : ℚ) : ℕ :=
  3 * GeneralPaperStoredScalarReadWork.overhead model A + 2 * GeneralPaperEncodedScalarStorage.natBits m +
    2 * rationalWordWidth coefficient + 256 * (A + 1)

theorem field {m : ℕ} (model : RationalCostModel) (S A layoutStart start : ℕ) (plan : GeneralPaperMeasuredBlockPlan.Plan)
    (full : Directory A) (installed : Installed A) (ctx : Context model S A layoutStart plan full installed)
    (route : GroupRoute m) (hRead : Readback model A installed (GeneralPaperRouteFieldCursor.expected model S A route start))
    (hHeaders : ∀ header ∈ (GeneralPaperRouteFieldCursor.expected model S A route start).headers,header ∈ full.headers)
    (hRoot : installed.root = (GeneralPaperRouteFieldCursor.expected model S A route start).root.reference)
    (index : Fin (GeneralPaperRouteFieldCursor.values route).length) :
    (GeneralPaperRecordScalarRead.read model A installed index.val).1 = some (GeneralPaperRouteFieldCursor.values route)[index.val] ∧
    (GeneralPaperRecordScalarRead.read model A installed index.val).2 ≤
      encode (GeneralPaperRouteFieldCursor.values route)[index.val] + GeneralPaperStoredScalarReadWork.overhead model A := by
  let directory := GeneralPaperRouteFieldCursor.expected model S A route start
  let header : Header A := ⟨directory.root,0,directory.cells.map (fun cell => cell.region.reference)⟩
  have hh : header ∈ full.headers := hHeaders header (List.mem_singleton_self _)
  have hValues := congrArg List.length (GeneralPaperRecordScalarRead.expected_values model S A start 16 (GeneralPaperRouteFieldCursor.values route))
  simp only [List.length_map] at hValues
  have hIndex : index.val < header.targets.length := by
    change index.val < (directory.cells.map (fun cell => cell.region.reference)).length
    rw [List.length_map]
    exact index.isLt.trans_le (le_of_eq hValues.symm)
  have hPointer := hRead.1 header (List.mem_singleton_self _) ⟨index.val,hIndex⟩
  change (GeneralPaperMixedReferenceRegionProgram.read model A (referenceMemory installed.memory) directory.root.reference 0 index.val).1 = _ at hPointer
  rw [← hRoot] at hPointer
  have hCount := GeneralPaperStoredReadContext.header_count_fits ctx header hh
  have hWork := GeneralPaperStoredReferenceReadWork.read_work model A A 0 index.val _ installed.root _
    (by decide) (hIndex.trans hCount) hPointer
  obtain ⟨hv,hw⟩ := GeneralPaperStoredRouteReadback.field model S A start installed route hRead hRoot index
  refine ⟨hv,?_⟩
  rw [hw]
  unfold GeneralPaperStoredScalarReadWork.overhead
  omega

theorem work {m : ℕ} (model : RationalCostModel) (S A layoutStart start : ℕ) (plan : GeneralPaperMeasuredBlockPlan.Plan)
    (full : Directory A) (installed : Installed A) (ctx : Context model S A layoutStart plan full installed)
    (route : GroupRoute m) (hRead : Readback model A installed (GeneralPaperRouteFieldCursor.expected model S A route start))
    (hHeaders : ∀ header ∈ (GeneralPaperRouteFieldCursor.expected model S A route start).headers,header ∈ full.headers)
    (hRoot : installed.root = (GeneralPaperRouteFieldCursor.expected model S A route start).root.reference) :
    (GeneralPaperRouteFieldRead.read model A installed).2 ≤ bound model A m route.2 := by
  rcases route with ⟨label,coefficient⟩
  cases label with
  | none =>
    have hFlag := field model S A layoutStart start plan full installed ctx (none,coefficient) hRead hHeaders hRoot ⟨0,by change 0 < 2; decide⟩
    have hCoefficient := field model S A layoutStart start plan full installed ctx (none,coefficient) hRead hHeaders hRoot ⟨1,by change 1 < 2; decide⟩
    rw [(GeneralPaperRouteFieldRead.absent model A installed coefficient hFlag.1 hCoefficient.1).2]
    simp only [GeneralPaperRouteFieldCursor.values,List.getElem_cons_zero,List.getElem_cons_succ,encode] at hFlag hCoefficient
    unfold bound
    dsimp only
    omega
  | some group =>
    have hFlag := field model S A layoutStart start plan full installed ctx (some group,coefficient) hRead hHeaders hRoot ⟨0,by change 0 < 3; decide⟩
    have hLabel := field model S A layoutStart start plan full installed ctx (some group,coefficient) hRead hHeaders hRoot ⟨1,by change 1 < 3; decide⟩
    have hCoefficient := field model S A layoutStart start plan full installed ctx (some group,coefficient) hRead hHeaders hRoot ⟨2,by change 2 < 3; decide⟩
    rw [(GeneralPaperRouteFieldRead.present model A installed group.val coefficient hFlag.1 hLabel.1 hCoefficient.1).2]
    have hGroup := binaryWordWidth_mono (Nat.le_of_lt group.isLt)
    simp only [GeneralPaperRouteFieldCursor.values,List.getElem_cons_zero,List.getElem_cons_succ,encode] at hFlag hLabel hCoefficient
    unfold bound GeneralPaperEncodedScalarStorage.natBits at *
    dsimp only
    omega

end Blotto.GeneralPaperStoredRouteFieldWork
