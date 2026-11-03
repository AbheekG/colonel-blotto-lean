import Blotto.GeneralPaperStoredReadContext

/-! Counted natural-list collection charges the sum of actual payload
encodings as well as address metadata. The measured owner derives all count and
increment widths; no source length executes in the actual collector. -/
namespace Blotto.GeneralPaperStoredNaturalCollectionWork
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperSamplerRecordInstallation (Readback)
open GeneralPaperRetainedScalarValue (Scalar)
open GeneralPaperFieldDirectory (Directory)
open GeneralPaperStoredReadContext (Context)
open GeneralPaperUnifiedFieldValue (referenceMemory)
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 8192

def perElement (model : RationalCostModel) (A : ℕ) : ℕ :=
  GeneralPaperStoredScalarReadWork.overhead model A + GeneralPaperStoredStreamWork.stepBound model A + 128 * (A + 1)

def bound (model : RationalCostModel) (A : ℕ) (values : List ℕ) : ℕ :=
  3 * (values.map GeneralPaperEncodedScalarStorage.natBits).sum + values.length * perElement model A + GeneralPaperStoredCountReadWork.bound model A + 192 * (A + 1)

theorem capacity (model : RationalCostModel) (S A start : ℕ) (values : List ℕ) (hA : 0 < A)
    (hOwner : (GeneralPaperRetainedHeaderCountSources.listHeader model S A start 32 1 (values.map Scalar.natural)).region.stop < 2 ^ A) :
    values.length + 1 < 2 ^ A := by
  change start + A * (1 * (values.map Scalar.natural).length + 32) < 2 ^ A at hOwner
  rw [List.length_map,Nat.one_mul] at hOwner
  nlinarith only [hA,hOwner]

theorem pointer (model : RationalCostModel) (S A start : ℕ) (installed : Installed A) (values : List ℕ)
    (hRead : Readback model A installed (GeneralPaperScalarRecordComponents.listExpected model S A start 32 1 (values.map Scalar.natural)))
    (hRoot : installed.root = (GeneralPaperScalarRecordComponents.listExpected model S A start 32 1 (values.map Scalar.natural)).root.reference)
    (index : Fin values.length) :
    ∃ target : FixedBinaryWord A,(GeneralPaperMixedReferenceRegionProgram.read model A (referenceMemory installed.memory) installed.root 32 index.val).1 =
      some (⟨A,target⟩ : GeneralPaperMixedReferenceMemory.Word) := by
  let header := GeneralPaperRetainedHeaderCountSources.listHeader model S A start 32 1 (values.map Scalar.natural)
  have hIndex : index.val < header.targets.length := by
    rw [GeneralPaperRetainedHeaderCountSources.list_target_count,List.length_map]
    exact index.isLt
  have h := hRead.1 header (List.mem_singleton_self _) ⟨index.val,hIndex⟩
  change (GeneralPaperMixedReferenceRegionProgram.read model A (referenceMemory installed.memory) header.region.reference 32 index.val).1 = _ at h
  change (GeneralPaperMixedReferenceRegionProgram.read model A (referenceMemory installed.memory)
    (GeneralPaperScalarRecordComponents.listExpected model S A start 32 1 (values.map Scalar.natural)).root.reference 32 index.val).1 = _ at h
  rw [← hRoot] at h
  exact ⟨_,h⟩

theorem each_work (model : RationalCostModel) (S A start : ℕ) (installed : Installed A) (values : List ℕ)
    (hRead : Readback model A installed (GeneralPaperScalarRecordComponents.listExpected model S A start 32 1 (values.map Scalar.natural)))
    (hRoot : installed.root = (GeneralPaperScalarRecordComponents.listExpected model S A start 32 1 (values.map Scalar.natural)).root.reference)
    (hCount : values.length < 2 ^ A) (index : Fin values.length) :
    (GeneralPaperStoredScalarRead.natural model A installed 32 index.val).2 ≤ 2 * GeneralPaperEncodedScalarStorage.natBits values[index.val] + GeneralPaperStoredScalarReadWork.overhead model A := by
  have h := GeneralPaperStoredScalarSourceRead.list model S A start 32 1 installed (values.map Scalar.natural) hRead hRoot
    ⟨index.val,by rw [List.length_map]; exact index.isLt⟩
  simp only [List.getElem_map] at h
  obtain ⟨target,hPointer⟩ := pointer model S A start installed values hRead hRoot index
  have hPointerWork := GeneralPaperStoredReferenceReadWork.read_work model A A 32 index.val _ installed.root target (by decide)
    (index.isLt.trans hCount) hPointer
  rw [(GeneralPaperStoredScalarRead.natural_of_scalar model A installed 32 index.val _ h.1).2,h.2]
  simp only [GeneralPaperRetainedScalarValue.encode] at *
  unfold GeneralPaperStoredScalarReadWork.overhead
  omega

theorem work (model : RationalCostModel) (S A layoutStart start : ℕ) (plan : GeneralPaperMeasuredBlockPlan.Plan)
    (full : Directory A) (installed : Installed A) (ctx : Context model S A layoutStart plan full installed) (values : List ℕ)
    (hRead : Readback model A installed (GeneralPaperScalarRecordComponents.listExpected model S A start 32 1 (values.map Scalar.natural)))
    (hHeader : GeneralPaperRetainedHeaderCountSources.listHeader model S A start 32 1 (values.map Scalar.natural) ∈ full.headers)
    (hRoot : installed.root = (GeneralPaperScalarRecordComponents.listExpected model S A start 32 1 (values.map Scalar.natural)).root.reference) :
    (GeneralPaperStoredReadStream.naturals model A installed 32).work ≤ bound model A values := by
  have hCount := capacity model S A start values ctx.positive (GeneralPaperStoredReadContext.header_capacity ctx _ hHeader)
  have hCountWork := GeneralPaperStoredCountReadWork.work model A installed full ctx.contract _ hHeader (by change (32 : ℕ) ≠ 0; decide)
  change (GeneralPaperHeaderCountReadback.count model A installed
    (GeneralPaperScalarRecordComponents.listExpected model S A start 32 1 (values.map Scalar.natural)).root.reference).2 ≤ _ at hCountWork
  rw [← hRoot] at hCountWork
  have hEach : ∀ index : Fin values.length,(GeneralPaperStoredScalarRead.natural model A installed 32 (0 + index.val)).2 ≤
      2 * GeneralPaperEncodedScalarStorage.natBits values[index.val] + GeneralPaperStoredScalarReadWork.overhead model A := by
    intro index
    simpa only [Nat.zero_add] using each_work model S A start installed values hRead hRoot (by omega) index
  have hPrice := GeneralPaperStoredStreamWork.price_bound model A (GeneralPaperStoredScalarRead.natural model A installed 32)
    GeneralPaperEncodedScalarStorage.natBits values 0 2 (GeneralPaperStoredScalarReadWork.overhead model A) (by omega) hEach
  rw [(GeneralPaperStoredReadStreamSources.naturals model S A start installed full ctx.contract values hRead hHeader hRoot).2.2]
  unfold bound perElement
  nlinarith only [hCountWork,hPrice]

end Blotto.GeneralPaperStoredNaturalCollectionWork
