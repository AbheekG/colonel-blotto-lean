import Blotto.GeneralPaperStoredListReadWork

/-! Complete indexed categorical-row access prices only the actual selected
row. The finite label bound is used in analysis, and every pointer/count fit
is derived from actual enclosing owners. -/
namespace Blotto.GeneralPaperStoredBooleanRowsWork
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperSamplerRecordInstallation (Readback)
open GeneralPaperFieldDirectory (Directory)
open GeneralPaperStoredReadContext (Context)
open GeneralPaperStoredChildRead (Child)
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 8192

def bound (model : RationalCostModel) (A w r : ℕ) : ℕ :=
  3 * GeneralPaperEncodedScalarStorage.natBits r + GeneralPaperStoredBooleanWordWork.bound model A w +
    3 * GeneralPaperStoredReferenceReadWork.readBound model A A + w + 1024 * (A + 1)

theorem work {r w : ℕ} (model : RationalCostModel) (S A layoutStart start : ℕ) (plan : GeneralPaperMeasuredBlockPlan.Plan)
    (full : Directory A) (installed : Installed A) (ctx : Context model S A layoutStart plan full installed) (rows : List (Fin r × FixedBinaryWord w))
    (hRead : Readback model A installed (GeneralPaperBooleanRowCursor.rowsExpected model S A start rows))
    (hHeaders : ∀ h ∈ (GeneralPaperBooleanRowCursor.rowsExpected model S A start rows).headers,h ∈ full.headers)
    (hRoot : installed.root = (GeneralPaperBooleanRowCursor.rowsExpected model S A start rows).root.reference) (index : Fin rows.length) :
    (GeneralPaperStoredBooleanRows.read model A installed index.val).2 ≤ bound model A w r := by
  obtain ⟨fieldStart,hLoad,_,hChildRead,hChildHeaders,_⟩ := GeneralPaperStoredListChildRead.child model A start installed
    (fun row => (GeneralPaperEqualMeasuredLeafPlans.row model S A row).sizes) (GeneralPaperBooleanRowCursor.expected model S A) rows hRead hRoot index
  let child := GeneralPaperBooleanRowCursor.expected model S A rows[index.val] fieldStart
  let loaded := GeneralPaperStoredScalarRead.atRoot installed child.root.reference
  have hRowWork := GeneralPaperStoredBooleanRowWork.work model S A layoutStart fieldStart plan full loaded
    (GeneralPaperStoredReadContext.atRoot ctx child.root.reference) rows[index.val] hChildRead
    (fun header hh => hHeaders header (hChildHeaders header hh)) rfl
  have hLoadWork := GeneralPaperStoredListReadWork.work model S A layoutStart start plan full installed ctx
    (fun row => (GeneralPaperEqualMeasuredLeafPlans.row model S A row).sizes) (GeneralPaperBooleanRowCursor.expected model S A) rows hRead hHeaders hRoot index
  have hLabel : GeneralPaperEncodedScalarStorage.natBits (rows[index.val]).1.val ≤ GeneralPaperEncodedScalarStorage.natBits r := by
    exact Nat.add_le_add_left (binaryWordWidth_mono (rows[index.val]).1.isLt.le) 1
  change (GeneralPaperStoredChildRead.load model A installed 32 index.val).1 = some (⟨A,loaded⟩ : Child) at hLoad
  rw [(GeneralPaperStoredBooleanRows.trace model A installed loaded index.val hLoad).2]
  unfold bound GeneralPaperStoredBooleanRowWork.bound at *
  omega

end Blotto.GeneralPaperStoredBooleanRowsWork
