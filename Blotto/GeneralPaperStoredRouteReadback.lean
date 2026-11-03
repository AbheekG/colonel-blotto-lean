import Blotto.GeneralPaperStoredSamplerGroups

/-! The existing route decoder works inside any retained combined memory.
Restricted readback proves its flag/optional label/coefficient without a
source route or a decoded field target among execution arguments. -/
namespace Blotto.GeneralPaperStoredRouteReadback
open GeneralPaperFieldDirectory GeneralPaperReferenceRegionSlots GeneralPaperRetainedScalarValue
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperSamplerRecordInstallation (Readback)
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 8192

theorem field {m : ℕ} (model : RationalCostModel) (S A start : ℕ) (installed : Installed A) (route : GroupRoute m)
    (hRead : Readback model A installed (GeneralPaperRouteFieldCursor.expected model S A route start))
    (hRoot : installed.root = (GeneralPaperRouteFieldCursor.expected model S A route start).root.reference)
    (index : Fin (GeneralPaperRouteFieldCursor.values route).length) :
    (GeneralPaperRecordScalarRead.read model A installed index.val).1 = some (GeneralPaperRouteFieldCursor.values route)[index.val] ∧
      (GeneralPaperRecordScalarRead.read model A installed index.val).2 =
        (GeneralPaperMixedReferenceRegionProgram.read model A (GeneralPaperUnifiedFieldValue.referenceMemory installed.memory) installed.root 0 index.val).2 +
        encode (GeneralPaperRouteFieldCursor.values route)[index.val] + 192 * A + 128 := by
  let directory := GeneralPaperRouteFieldCursor.expected model S A route start
  let header : Header A := ⟨directory.root,0,directory.cells.map (fun cell => cell.region.reference)⟩
  exact GeneralPaperStoredScalarSourceRead.fields model A installed directory hRead header (List.mem_singleton_self _)
    directory.cells (GeneralPaperRouteFieldCursor.values route) (fun _ hc => hc) rfl
    (GeneralPaperRecordScalarRead.expected_values model S A start 16 (GeneralPaperRouteFieldCursor.values route)) hRoot index

theorem source {m : ℕ} (model : RationalCostModel) (S A start : ℕ) (installed : Installed A) (route : GroupRoute m)
    (hRead : Readback model A installed (GeneralPaperRouteFieldCursor.expected model S A route start))
    (hRoot : installed.root = (GeneralPaperRouteFieldCursor.expected model S A route start).root.reference) :
    (GeneralPaperRouteFieldRead.read model A installed).1 = some (route.1.map Fin.val,route.2) :=
  GeneralPaperRouteFieldRead.source_of_fields model A installed route (fun index => (field model S A start installed route hRead hRoot index).1)

end Blotto.GeneralPaperStoredRouteReadback
