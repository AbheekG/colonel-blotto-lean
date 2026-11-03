import Blotto.GeneralPaperStoredReferenceReadWork

/-! Payload-sensitive costs for the actual scalar readers. Reference
metadata has a bound depending only on the address width; complete scalar
copies remain proportional to the selected stored payload's own encoding. -/
namespace Blotto.GeneralPaperStoredScalarReadWork
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperSamplerRecordInstallation (Readback)
open GeneralPaperRetainedScalarValue (Scalar)
open GeneralPaperFieldDirectory (ofArray)
open GeneralPaperUnifiedFieldValue
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 8192

def overhead (model : RationalCostModel) (A : ℕ) : ℕ :=
  GeneralPaperStoredReferenceReadWork.readBound model A A + 256 * (A + 1)

theorem array_pointer {model : RationalCostModel} {S A start : ℕ} {installed : Installed A} {values : List Scalar}
    (hRead : Readback model A installed (ofArray (GeneralPaperMappedScalarArrayCursor.expected model S A start values)))
    (hRoot : installed.root = (GeneralPaperMappedScalarArrayCursor.expected model S A start values).header.region.reference)
    (index : Fin values.length) :
    ∃ target : FixedBinaryWord A,(GeneralPaperMixedReferenceRegionProgram.read model A (referenceMemory installed.memory) installed.root 64 index.val).1 =
      some (⟨A,target⟩ : GeneralPaperMixedReferenceMemory.Word) := by
  let fields := GeneralPaperMappedScalarArrayCursor.expected model S A start values
  have hIndex : index.val < fields.header.targets.length := by
    rw [GeneralPaperFieldDirectoryLookup.array_target_count model S A start values]
    exact index.isLt
  have h := hRead.1 fields.header (List.mem_singleton_self _) ⟨index.val,hIndex⟩
  change (GeneralPaperMixedReferenceRegionProgram.read model A (referenceMemory installed.memory) fields.header.region.reference 64 index.val).1 = _ at h
  rw [← hRoot] at h
  exact ⟨_,h⟩

theorem array_work (model : RationalCostModel) (S A start : ℕ) (installed : Installed A) (values : List Scalar)
    (hRead : Readback model A installed (ofArray (GeneralPaperMappedScalarArrayCursor.expected model S A start values)))
    (hRoot : installed.root = (GeneralPaperMappedScalarArrayCursor.expected model S A start values).header.region.reference)
    (hCount : values.length < 2 ^ A) (index : Fin values.length) :
    (GeneralPaperStoredScalarRead.read model A installed 64 index.val).2 ≤ GeneralPaperRetainedScalarValue.encode values[index.val] + overhead model A := by
  obtain ⟨target,hPointer⟩ := array_pointer hRead hRoot index
  have hPointerWork := GeneralPaperStoredReferenceReadWork.read_work model A A 64 index.val _ installed.root target le_rfl
    (index.isLt.trans hCount) hPointer
  rw [(GeneralPaperStoredScalarSourceRead.array model S A start installed values hRead hRoot index).2]
  unfold overhead
  omega

theorem rational_array_work {n : ℕ} (model : RationalCostModel) (S A start : ℕ) (installed : Installed A) (source : FixedArrayTable n ℚ)
    (hRead : Readback model A installed (ofArray (GeneralPaperMappedScalarArrayCursor.expected model S A start (source.data.toList.map Scalar.rational))))
    (hRoot : installed.root = (GeneralPaperMappedScalarArrayCursor.expected model S A start (source.data.toList.map Scalar.rational)).header.region.reference)
    (hCount : n < 2 ^ A) (index : Fin n) :
    (GeneralPaperStoredScalarRead.rational model A installed 64 index.val).2 ≤ 2 * rationalWordWidth (source.read index) + overhead model A := by
  let values := source.data.toList.map Scalar.rational
  have hi : index.val < values.length := by rw [List.length_map,Array.length_toList,source.size]; exact index.isLt
  have h := GeneralPaperStoredScalarSourceRead.array model S A start installed values hRead hRoot ⟨index.val,hi⟩
  have hValue : values[index.val] = Scalar.rational (source.read index) := by simp only [values,List.getElem_map,Array.getElem_toList,FixedArrayTable.read]
  rw [hValue] at h
  obtain ⟨target,hPointer⟩ := array_pointer hRead hRoot ⟨index.val,hi⟩
  have hPointerWork := GeneralPaperStoredReferenceReadWork.read_work model A A 64 index.val _ installed.root target le_rfl
    (index.isLt.trans hCount) hPointer
  rw [(GeneralPaperStoredScalarRead.rational_of_scalar model A installed 64 index.val _ h.1).2,h.2]
  simp only [GeneralPaperRetainedScalarValue.encode] at *
  unfold overhead
  omega

theorem bit_work (model : RationalCostModel) (A fixed index : ℕ) (installed : Installed A)
    (root : FixedBinaryWord A) (value : Bool)
    (hFixed : fixed ≤ 64) (hIndex : index < 2 ^ A)
    (hPointer : (GeneralPaperMixedReferenceRegionProgram.read model A (referenceMemory installed.memory) installed.root fixed index).1 =
      some (⟨A,root⟩ : GeneralPaperMixedReferenceMemory.Word))
    (hValue : (GeneralPaperPayloadMemory.read A GeneralPaperRetainedScalarValue.encode (scalarMemory installed.memory) root).1 = some (.bit value)) :
    (GeneralPaperStoredScalarRead.bit model A installed fixed index).2 ≤ 2 + overhead model A := by
  have h := GeneralPaperStoredScalarRead.trace model A installed fixed index root (.bit value) hPointer hValue
  have hPointerWork := GeneralPaperStoredReferenceReadWork.read_work model A A fixed index _ installed.root root hFixed hIndex hPointer
  rw [(GeneralPaperStoredScalarRead.bit_of_scalar model A installed fixed index value h.1).2,h.2]
  simp only [GeneralPaperRetainedScalarValue.encode] at *
  unfold overhead
  omega

end Blotto.GeneralPaperStoredScalarReadWork
