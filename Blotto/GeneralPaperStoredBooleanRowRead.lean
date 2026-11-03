import Blotto.GeneralPaperStoredSamplerControls

/-! Label and count word come from a retained row record. The reader has no
source row, finite-label bound or external word width among its arguments. -/
namespace Blotto.GeneralPaperStoredBooleanRowRead
open GeneralPaperFieldDirectory GeneralPaperRetainedScalarValue
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperSamplerRecordInstallation (Readback)
open GeneralPaperHeaderCountInstallation (Contract)
open GeneralPaperUnifiedFieldValue
open GeneralPaperMixedReferenceMemory (Word)
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 8192

def read (model : RationalCostModel) (A : ℕ) (installed : Installed A) : Option (ℕ × Word) × ℕ :=
  let label := GeneralPaperStoredScalarRead.natural model A installed 0 0
  match label.1 with
  | none => (none,label.2 + 64 * (A + 1))
  | some value =>
    let word := GeneralPaperStoredRecordCollectors.word model A installed 1
    match word.1 with
    | none => (none,label.2 + word.2 + 64 * (A + 1))
    | some bits => (some (value,bits),label.2 + word.2 + GeneralPaperEncodedScalarStorage.natBits value + bits.1 + 128 * (A + 1))

theorem trace (model : RationalCostModel) (A : ℕ) (installed : Installed A) (label : ℕ) (word : Word)
    (hLabel : (GeneralPaperStoredScalarRead.natural model A installed 0 0).1 = some label)
    (hWord : (GeneralPaperStoredRecordCollectors.word model A installed 1).1 = some word) :
    (read model A installed).1 = some (label,word) ∧
      (read model A installed).2 = (GeneralPaperStoredScalarRead.natural model A installed 0 0).2 +
        (GeneralPaperStoredRecordCollectors.word model A installed 1).2 +
        GeneralPaperEncodedScalarStorage.natBits label + word.1 + 128 * (A + 1) := by
  simp only [read,hLabel,hWord,and_self]

theorem source {r w : ℕ} (model : RationalCostModel) (S A start : ℕ) (installed : Installed A) (full : Directory A)
    (hContract : Contract model A installed full) (row : Fin r × FixedBinaryWord w)
    (hRead : Readback model A installed (GeneralPaperBooleanRowCursor.expected model S A row start))
    (hHeaders : ∀ header ∈ (GeneralPaperBooleanRowCursor.expected model S A row start).headers,header ∈ full.headers)
    (hRoot : installed.root = (GeneralPaperBooleanRowCursor.expected model S A row start).root.reference) :
    (read model A installed).1 = some (row.1.val,(⟨w,row.2⟩ : Word)) ∧
      (read model A installed).2 = (GeneralPaperStoredScalarRead.natural model A installed 0 0).2 +
        (GeneralPaperStoredRecordCollectors.word model A installed 1).2 +
        GeneralPaperEncodedScalarStorage.natBits row.1.val + w + 128 * (A + 1) := by
  obtain ⟨labelStart,_,hLabelPointer,hLabelRead,_,_⟩ := GeneralPaperStoredChildRead.record_child model A start 16 installed
    (GeneralPaperBooleanRowCursor.schema model S A row) (GeneralPaperBooleanRowCursor.child model S A row)
    GeneralPaperBooleanRowCursor.fields hRead hRoot ⟨0,by decide⟩
  let labelChild := GeneralPaperBooleanRowCursor.child model S A row .label labelStart
  let cell : GeneralPaperScalarFieldCursor.Cell A := ⟨labelChild.root,.natural row.1.val⟩
  have hScalar := (hLabelRead.2 cell (List.mem_singleton_self _)).1
  have hLabelValue := (GeneralPaperStoredScalarRead.trace model A installed 0 0 labelChild.root.reference (.natural row.1.val)
    hLabelPointer hScalar).1
  have hLabel := (GeneralPaperStoredScalarRead.natural_of_scalar model A installed 0 0 row.1.val hLabelValue).1
  obtain ⟨wordStart,hWordLoad,_,hWordRead,hWordHeaders,_⟩ := GeneralPaperStoredChildRead.record_child model A start 16 installed
    (GeneralPaperBooleanRowCursor.schema model S A row) (GeneralPaperBooleanRowCursor.child model S A row)
    GeneralPaperBooleanRowCursor.fields hRead hRoot ⟨1,by decide⟩
  let wordChild := GeneralPaperBooleanRowCursor.child model S A row .word wordStart
  let loaded := GeneralPaperStoredScalarRead.atRoot installed wordChild.root.reference
  have hWordContract : Contract model A loaded full := hContract
  have hWord := (GeneralPaperStoredBooleanWordSourceRead.source model S A wordStart loaded full hWordContract row.2
    hWordRead (fun header hh => hHeaders header (hWordHeaders header hh)) rfl).1
  have hSelected := (GeneralPaperStoredRecordCollectors.word_trace model A installed loaded 1 hWordLoad).1.trans hWord
  exact trace model A installed row.1.val ⟨w,row.2⟩ hLabel hSelected

end Blotto.GeneralPaperStoredBooleanRowRead
