import Blotto.GeneralPaperStoredListChildRead

/-! An indexed Boolean-row read follows one stored list reference, then the
actual row label and word. No other row is reconstructed by this operation. -/
namespace Blotto.GeneralPaperStoredBooleanRows
open GeneralPaperFieldDirectory
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperSamplerRecordInstallation (Readback)
open GeneralPaperHeaderCountInstallation (Contract)
open GeneralPaperStoredChildRead (Child)
open GeneralPaperMixedReferenceMemory (Word)
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 8192

def read (model : RationalCostModel) (A : ℕ) (installed : Installed A) (index : ℕ) : Option (ℕ × Word) × ℕ :=
  let child := GeneralPaperStoredChildRead.load model A installed 32 index
  match child.1 with
  | none => (none,child.2 + 64 * (A + 1))
  | some ⟨B,loaded⟩ =>
    let actual := GeneralPaperStoredBooleanRowRead.read model B loaded
    (actual.1,child.2 + actual.2 + 64 * (A + B + 1))

theorem trace (model : RationalCostModel) (A : ℕ) (installed loaded : Installed A) (index : ℕ)
    (hChild : (GeneralPaperStoredChildRead.load model A installed 32 index).1 = some (⟨A,loaded⟩ : Child)) :
    (read model A installed index).1 = (GeneralPaperStoredBooleanRowRead.read model A loaded).1 ∧
      (read model A installed index).2 = (GeneralPaperStoredChildRead.load model A installed 32 index).2 +
        (GeneralPaperStoredBooleanRowRead.read model A loaded).2 + 128 * A + 64 := by
  simp only [read,hChild]
  constructor
  · exact True.intro
  · ring

theorem source {r w : ℕ} (model : RationalCostModel) (S A start : ℕ) (installed : Installed A) (full : Directory A)
    (hContract : Contract model A installed full) (rows : List (Fin r × FixedBinaryWord w))
    (hRead : Readback model A installed (GeneralPaperBooleanRowCursor.rowsExpected model S A start rows))
    (hHeaders : ∀ header ∈ (GeneralPaperBooleanRowCursor.rowsExpected model S A start rows).headers,header ∈ full.headers)
    (hRoot : installed.root = (GeneralPaperBooleanRowCursor.rowsExpected model S A start rows).root.reference)
    (index : Fin rows.length) :
    ∃ root : FixedBinaryWord A,
      (read model A installed index.val).1 = some ((rows[index.val]).1.val,(⟨w,(rows[index.val]).2⟩ : Word)) ∧
      (read model A installed index.val).2 = (GeneralPaperStoredChildRead.load model A installed 32 index.val).2 +
        (GeneralPaperStoredBooleanRowRead.read model A (GeneralPaperStoredScalarRead.atRoot installed root)).2 + 128 * A + 64 := by
  obtain ⟨fieldStart,hLoad,_,hChildRead,hChildHeaders,_⟩ := GeneralPaperStoredListChildRead.child model A start installed
    (fun row => (GeneralPaperEqualMeasuredLeafPlans.row model S A row).sizes)
    (GeneralPaperBooleanRowCursor.expected model S A) rows hRead hRoot index
  let child := GeneralPaperBooleanRowCursor.expected model S A rows[index.val] fieldStart
  let loaded := GeneralPaperStoredScalarRead.atRoot installed child.root.reference
  have hChildContract : Contract model A loaded full := hContract
  have hv := (GeneralPaperStoredBooleanRowRead.source model S A fieldStart loaded full hChildContract rows[index.val]
    hChildRead (fun header hh => hHeaders header (hChildHeaders header hh)) rfl).1
  obtain ⟨hData,hWork⟩ := trace model A installed loaded index.val hLoad
  exact ⟨child.root.reference,hData.trans hv,hWork⟩

theorem count_source {r w : ℕ} (model : RationalCostModel) (S A start : ℕ) (installed : Installed A) (full : Directory A)
    (hContract : Contract model A installed full) (rows : List (Fin r × FixedBinaryWord w))
    (hHeaders : ∀ header ∈ (GeneralPaperBooleanRowCursor.rowsExpected model S A start rows).headers,header ∈ full.headers)
    (hRoot : installed.root = (GeneralPaperBooleanRowCursor.rowsExpected model S A start rows).root.reference) :
    (GeneralPaperHeaderCountReadback.count model A installed installed.root).1 = some rows.length :=
  GeneralPaperStoredListChildRead.count_source model A start installed full hContract _ _ rows hHeaders hRoot

end Blotto.GeneralPaperStoredBooleanRows
