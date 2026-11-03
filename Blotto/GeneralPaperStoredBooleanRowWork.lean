import Blotto.GeneralPaperStoredBooleanWorkRates

/-! One reached categorical row follows its actual label scalar and word
record. Payload-sensitive label and complete word reconstruction prices
compose in the same measured enclosing memory. -/
namespace Blotto.GeneralPaperStoredBooleanRowWork
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperSamplerRecordInstallation (Readback)
open GeneralPaperFieldDirectory (Directory)
open GeneralPaperRetainedScalarValue (Scalar)
open GeneralPaperStoredReadContext (Context)
open GeneralPaperStoredChildRead (Child)
open GeneralPaperUnifiedFieldValue (referenceMemory scalarMemory)
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 8192

def bound (model : RationalCostModel) (A w label : ℕ) : ℕ :=
  3 * GeneralPaperEncodedScalarStorage.natBits label + GeneralPaperStoredBooleanWordWork.bound model A w +
    2 * GeneralPaperStoredReferenceReadWork.readBound model A A + w + 768 * (A + 1)

theorem label_work (model : RationalCostModel) (A : ℕ) (installed : Installed A) (root : FixedBinaryWord A) (label : ℕ)
    (hPointer : (GeneralPaperMixedReferenceRegionProgram.read model A (referenceMemory installed.memory) installed.root 0 0).1 =
      some (⟨A,root⟩ : GeneralPaperMixedReferenceMemory.Word))
    (hScalar : (GeneralPaperPayloadMemory.read A GeneralPaperRetainedScalarValue.encode (scalarMemory installed.memory) root).1 = some (.natural label)) :
    (GeneralPaperStoredScalarRead.natural model A installed 0 0).2 ≤
      2 * GeneralPaperEncodedScalarStorage.natBits label + GeneralPaperStoredScalarReadWork.overhead model A := by
  have h := GeneralPaperStoredScalarRead.trace model A installed 0 0 root (.natural label) hPointer hScalar
  have hPointerWork := GeneralPaperStoredReferenceReadWork.read_work model A A 0 0 _ installed.root root
    (by decide) (Nat.two_pow_pos A) hPointer
  rw [(GeneralPaperStoredScalarRead.natural_of_scalar model A installed 0 0 label h.1).2,h.2]
  simp only [GeneralPaperRetainedScalarValue.encode] at *
  unfold GeneralPaperStoredScalarReadWork.overhead
  omega

theorem work {r w : ℕ} (model : RationalCostModel) (S A layoutStart start : ℕ) (plan : GeneralPaperMeasuredBlockPlan.Plan)
    (full : Directory A) (installed : Installed A) (ctx : Context model S A layoutStart plan full installed) (row : Fin r × FixedBinaryWord w)
    (hRead : Readback model A installed (GeneralPaperBooleanRowCursor.expected model S A row start))
    (hHeaders : ∀ header ∈ (GeneralPaperBooleanRowCursor.expected model S A row start).headers,header ∈ full.headers)
    (hRoot : installed.root = (GeneralPaperBooleanRowCursor.expected model S A row start).root.reference) :
    (GeneralPaperStoredBooleanRowRead.read model A installed).2 ≤ bound model A w row.1.val := by
  obtain ⟨labelStart,_,hLabelPointer,hLabelRead,_,_⟩ := GeneralPaperStoredChildRead.record_child model A start 16 installed
    (GeneralPaperBooleanRowCursor.schema model S A row) (GeneralPaperBooleanRowCursor.child model S A row)
    GeneralPaperBooleanRowCursor.fields hRead hRoot ⟨0,by decide⟩
  let labelChild := GeneralPaperBooleanRowCursor.child model S A row .label labelStart
  let cell : GeneralPaperScalarFieldCursor.Cell A := ⟨labelChild.root,.natural row.1.val⟩
  have hScalar := (hLabelRead.2 cell (List.mem_singleton_self _)).1
  have hLabelWork := label_work model A installed labelChild.root.reference row.1.val hLabelPointer hScalar
  obtain ⟨wordStart,hLoad,_,hWordRead,hWordHeaders,_⟩ := GeneralPaperStoredChildRead.record_child model A start 16 installed
    (GeneralPaperBooleanRowCursor.schema model S A row) (GeneralPaperBooleanRowCursor.child model S A row)
    GeneralPaperBooleanRowCursor.fields hRead hRoot ⟨1,by decide⟩
  let wordChild := GeneralPaperBooleanRowCursor.child model S A row .word wordStart
  let loaded := GeneralPaperStoredScalarRead.atRoot installed wordChild.root.reference
  have hWordWork := GeneralPaperStoredBooleanWordWork.work model S A layoutStart wordStart plan full loaded
    (GeneralPaperStoredReadContext.atRoot ctx wordChild.root.reference) row.2 hWordRead
    (fun header hh => hHeaders header (hWordHeaders header hh)) rfl
  have hLoadWork := GeneralPaperStoredRecordReadWork.work model S A layoutStart start 16 plan full installed ctx
    (GeneralPaperBooleanRowCursor.schema model S A row) (GeneralPaperBooleanRowCursor.child model S A row)
    GeneralPaperBooleanRowCursor.fields hRead hHeaders hRoot ⟨1,by decide⟩
  change (GeneralPaperStoredChildRead.load model A installed 0 1).1 = some (⟨A,loaded⟩ : Child) at hLoad
  change (GeneralPaperStoredChildRead.load model A installed 0 1).2 ≤ _ at hLoadWork
  have hWordPrice := (GeneralPaperStoredRecordCollectors.word_trace model A installed loaded 1 hLoad).2
  rw [(GeneralPaperStoredBooleanRowRead.source model S A start installed full ctx.contract row hRead hHeaders hRoot).2,hWordPrice]
  unfold bound GeneralPaperStoredScalarReadWork.overhead at *
  omega

end Blotto.GeneralPaperStoredBooleanRowWork
