import Blotto.GeneralPaperStoredSamplerMidpoint

/-! A selected segment endpoint follows the actual left/right matrix child
and reads only its selected row. Source matrices and dimensions occur solely
in erased correctness statements. -/
namespace Blotto.GeneralPaperStoredEndpointRows
open GeneralPaperFieldDirectory
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperSamplerRecordInstallation (Readback)
open GeneralPaperHeaderCountInstallation (Contract)
open GeneralPaperStoredChildRead (Child)
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 8192

inductive Side where | left | right

def slot : Side → Fin GeneralPaperSegmentRecordCursor.fields.length
  | .left => ⟨1,by decide⟩
  | .right => ⟨2,by decide⟩

def matrix {m r : ℕ} {l : RationalSegmentLottery m r} (source : PreparedSegmentDescriptor l) :
    Side → FixedArrayTable r (FixedArrayTable m ℚ)
  | .left => source.left
  | .right => source.right

theorem selected_child {m r : ℕ} {l : RationalSegmentLottery m r} (model : RationalCostModel) (S A start : ℕ)
    (source : PreparedSegmentDescriptor l) (side : Side) :
    GeneralPaperSegmentRecordCursor.child model S A source (GeneralPaperSegmentRecordCursor.fields[(slot side).val]) start =
      GeneralPaperMatrixFieldCursor.expected model S A start (matrix source side) := by cases side <;> rfl

def read (model : RationalCostModel) (A : ℕ) (installed : Installed A) (side : Side) (index : ℕ) : GeneralPaperStoredReadStream.Result ℚ :=
  let child := GeneralPaperStoredChildRead.load model A installed 0 (slot side).val
  match child.1 with
  | none => ⟨none,0,child.2 + 64 * (A + 1)⟩
  | some ⟨B,loaded⟩ =>
    let actual := GeneralPaperStoredMatrixRowRead.read model B loaded index
    ⟨actual.values,actual.count,child.2 + actual.work + 64 * (A + B + 1)⟩

theorem trace (model : RationalCostModel) (A : ℕ) (installed loaded : Installed A) (side : Side) (index : ℕ)
    (hChild : (GeneralPaperStoredChildRead.load model A installed 0 (slot side).val).1 = some (⟨A,loaded⟩ : Child)) :
    (read model A installed side index).values = (GeneralPaperStoredMatrixRowRead.read model A loaded index).values ∧
      (read model A installed side index).count = (GeneralPaperStoredMatrixRowRead.read model A loaded index).count ∧
      (read model A installed side index).work = (GeneralPaperStoredChildRead.load model A installed 0 (slot side).val).2 +
        (GeneralPaperStoredMatrixRowRead.read model A loaded index).work + 128 * A + 64 := by
  simp only [read,hChild]
  refine ⟨True.intro,True.intro,?_⟩
  ring

theorem source {m r : ℕ} {l : RationalSegmentLottery m r} (model : RationalCostModel) (S A start : ℕ)
    (installed : Installed A) (full : Directory A) (hContract : Contract model A installed full)
    (descriptor : PreparedSegmentDescriptor l)
    (hRead : Readback model A installed (GeneralPaperSegmentRecordCursor.expected model S A descriptor start))
    (hHeaders : ∀ header ∈ (GeneralPaperSegmentRecordCursor.expected model S A descriptor start).headers,header ∈ full.headers)
    (hRoot : installed.root = (GeneralPaperSegmentRecordCursor.expected model S A descriptor start).root.reference)
    (side : Side) (index : Fin r) :
    ∃ root : FixedBinaryWord A,
      (read model A installed side index.val).values = some ((matrix descriptor side).read index).data.toList ∧
      (read model A installed side index.val).count = m ∧
      (read model A installed side index.val).work = (GeneralPaperStoredChildRead.load model A installed 0 (slot side).val).2 +
        (GeneralPaperStoredMatrixRowRead.read model A (GeneralPaperStoredScalarRead.atRoot installed root) index.val).work + 128 * A + 64 := by
  obtain ⟨fieldStart,hLoad,_,hChildRead,hChildHeaders,_⟩ := GeneralPaperStoredChildRead.record_child model A start 32 installed
    (GeneralPaperSegmentRecordCursor.schema model S A descriptor) (GeneralPaperSegmentRecordCursor.child model S A descriptor)
    GeneralPaperSegmentRecordCursor.fields hRead hRoot (slot side)
  simp only [selected_child] at hLoad hChildRead hChildHeaders
  let child := GeneralPaperMatrixFieldCursor.expected model S A fieldStart (matrix descriptor side)
  let loaded := GeneralPaperStoredScalarRead.atRoot installed child.root.reference
  have hChildContract : Contract model A loaded full := hContract
  obtain ⟨_,hv,hc,_⟩ := GeneralPaperStoredMatrixRowRead.source model S A fieldStart loaded full hChildContract
    (matrix descriptor side) hChildRead (fun header hh => hHeaders header (hChildHeaders header hh)) rfl index
  obtain ⟨hData,hCount,hWork⟩ := trace model A installed loaded side index.val hLoad
  exact ⟨child.root.reference,hData.trans hv,hCount.trans hc,hWork⟩

end Blotto.GeneralPaperStoredEndpointRows
