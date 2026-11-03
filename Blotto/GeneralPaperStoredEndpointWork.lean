import Blotto.GeneralPaperStoredMatrixRowWork
import Blotto.GeneralPaperStoredRecordReadWork
import Blotto.GeneralPaperStoredEndpointRows

/-! Each endpoint read follows the selected side and selected row. Complete
costs and both index capacities derive from the same enclosing measured heap. -/
namespace Blotto.GeneralPaperStoredEndpointWork
open GeneralPaperFieldDirectory
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperSamplerRecordInstallation (Readback)
open GeneralPaperStoredReadContext (Context)
open GeneralPaperStoredEndpointRows (Side matrix slot)
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192

def bound {m : ℕ} (model : RationalCostModel) (A : ℕ) (row : FixedArrayTable m ℚ) : ℕ :=
  GeneralPaperStoredMatrixRowWork.bound model A row +
    GeneralPaperStoredReferenceReadWork.readBound model A A + 256 * (A + 1)

def heightBound (model : RationalCostModel) (A m s : ℕ) : ℕ :=
  3 * (m * (1 + 2 * s)) + m * GeneralPaperStoredRationalCollectionWork.perElement model A +
    GeneralPaperStoredCountReadWork.bound model A + 2 * GeneralPaperStoredReferenceReadWork.readBound model A A + 704 * (A + 1)

theorem height_bound {m : ℕ} (model : RationalCostModel) (A s : ℕ) (row : FixedArrayTable m ℚ)
    (h : ∀ g,RationalHeight (row.read g) s) : bound model A row ≤ heightBound model A m s := by
  have hPayload : (row.data.toList.map rationalWordWidth).sum ≤ m * (1 + 2 * s) := by
    rw [← GeneralPaperRowPrefix.list_ofFn row,List.map_ofFn,List.sum_ofFn]
    calc
      _ ≤ ∑ _g : Fin m,(1 + 2 * s) := Finset.sum_le_sum (fun g _ => rationalWordWidth_of_height (h g))
      _ = _ := by simp
  unfold bound heightBound GeneralPaperStoredMatrixRowWork.bound GeneralPaperStoredRationalCollectionWork.bound
  omega

theorem bounds {m r : ℕ} {l : RationalSegmentLottery m r} (model : RationalCostModel)
    (S A layoutStart start : ℕ) (plan : GeneralPaperMeasuredBlockPlan.Plan) (full : Directory A)
    (installed : Installed A) (ctx : Context model S A layoutStart plan full installed) (descriptor : PreparedSegmentDescriptor l)
    (hRead : Readback model A installed (GeneralPaperSegmentRecordCursor.expected model S A descriptor start))
    (hHeaders : ∀ header ∈ (GeneralPaperSegmentRecordCursor.expected model S A descriptor start).headers,header ∈ full.headers)
    (hRoot : installed.root = (GeneralPaperSegmentRecordCursor.expected model S A descriptor start).root.reference)
    (side : Side) (index : Fin r) :
    m + 1 < 2 ^ A ∧ (GeneralPaperStoredEndpointRows.read model A installed side index.val).work ≤ bound model A ((matrix descriptor side).read index) := by
  obtain ⟨fieldStart,hLoad,_,hChildRead,hChildHeaders,_⟩ := GeneralPaperStoredChildRead.record_child model A start 32 installed
    (GeneralPaperSegmentRecordCursor.schema model S A descriptor) (GeneralPaperSegmentRecordCursor.child model S A descriptor)
    GeneralPaperSegmentRecordCursor.fields hRead hRoot (slot side)
  simp only [GeneralPaperStoredEndpointRows.selected_child] at hLoad hChildRead hChildHeaders
  let child := GeneralPaperMatrixFieldCursor.expected model S A fieldStart (matrix descriptor side)
  let loaded := GeneralPaperStoredScalarRead.atRoot installed child.root.reference
  have hRow := GeneralPaperStoredMatrixRowWork.bounds model S A layoutStart fieldStart plan loaded full
    (GeneralPaperStoredReadContext.atRoot ctx child.root.reference) (matrix descriptor side) hChildRead
    (fun header hh => hHeaders header (hChildHeaders header hh)) rfl index
  have hLoadWork := GeneralPaperStoredRecordReadWork.work model S A layoutStart start 32 plan full installed ctx
    (GeneralPaperSegmentRecordCursor.schema model S A descriptor) (GeneralPaperSegmentRecordCursor.child model S A descriptor)
    GeneralPaperSegmentRecordCursor.fields hRead hHeaders hRoot (slot side)
  change (GeneralPaperStoredChildRead.load model A installed 0 (slot side).val).1 =
    some (⟨A,loaded⟩ : GeneralPaperStoredChildRead.Child) at hLoad
  change (GeneralPaperStoredChildRead.load model A installed 0 (slot side).val).2 ≤ _ at hLoadWork
  obtain ⟨hExtent,hRow⟩ := hRow
  refine ⟨hExtent,?_⟩
  rw [(GeneralPaperStoredEndpointRows.trace model A installed loaded side index.val hLoad).2.2]
  unfold bound
  omega

end Blotto.GeneralPaperStoredEndpointWork
