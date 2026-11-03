import Blotto.GeneralPaperStoredReadStream

/-! Counted collectors recover actual retained source fields inside a larger
memory. Counts come from the initialized header; element proofs come from
restricted old-slot readback. No source data or length is a collector input. -/
namespace Blotto.GeneralPaperStoredReadStreamSources
open GeneralPaperFieldDirectory GeneralPaperRetainedScalarValue
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperSamplerRecordInstallation (Readback)
open GeneralPaperHeaderCountInstallation (Contract)
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 8192

theorem scalar_array (model : RationalCostModel) (S A start : ℕ) (installed : Installed A) (full : Directory A)
    (hContract : Contract model A installed full) (values : List Scalar)
    (hRead : Readback model A installed (ofArray (GeneralPaperMappedScalarArrayCursor.expected model S A start values)))
    (hHeader : (GeneralPaperMappedScalarArrayCursor.expected model S A start values).header ∈ full.headers)
    (hRoot : installed.root = (GeneralPaperMappedScalarArrayCursor.expected model S A start values).header.region.reference) :
    (GeneralPaperStoredReadStream.scalars model A installed 64).values = some values ∧
      (GeneralPaperStoredReadStream.scalars model A installed 64).count = values.length ∧
      (GeneralPaperStoredReadStream.scalars model A installed 64).work =
        (GeneralPaperHeaderCountReadback.count model A installed installed.root).2 +
        GeneralPaperStoredReadStream.price model A (GeneralPaperStoredScalarRead.read model A installed 64)
          GeneralPaperRetainedScalarValue.encode 0 values + 128 * (A + 1) := by
  have hc := GeneralPaperRetainedHeaderCountSources.scalar_array model S A start installed full hContract values hHeader
  rw [← hRoot] at hc
  exact GeneralPaperStoredReadStream.counted_source model A installed _ _ values hc
    (fun index => (GeneralPaperStoredScalarSourceRead.array model S A start installed values hRead hRoot index).1)

theorem scalar_list (model : RationalCostModel) (S A start fixed stride : ℕ) (installed : Installed A) (full : Directory A)
    (hContract : Contract model A installed full) (values : List Scalar)
    (hRead : Readback model A installed (GeneralPaperScalarRecordComponents.listExpected model S A start fixed stride values))
    (hHeader : GeneralPaperRetainedHeaderCountSources.listHeader model S A start fixed stride values ∈ full.headers) (hf : fixed ≠ 0)
    (hRoot : installed.root = (GeneralPaperScalarRecordComponents.listExpected model S A start fixed stride values).root.reference) :
    (GeneralPaperStoredReadStream.scalars model A installed fixed).values = some values ∧
      (GeneralPaperStoredReadStream.scalars model A installed fixed).count = values.length ∧
      (GeneralPaperStoredReadStream.scalars model A installed fixed).work =
        (GeneralPaperHeaderCountReadback.count model A installed installed.root).2 +
        GeneralPaperStoredReadStream.price model A (GeneralPaperStoredScalarRead.read model A installed fixed)
          GeneralPaperRetainedScalarValue.encode 0 values + 128 * (A + 1) := by
  have hc := GeneralPaperRetainedHeaderCountSources.scalar_list model S A start fixed stride installed full hContract values hf hHeader
  change (GeneralPaperHeaderCountReadback.count model A installed
    (GeneralPaperScalarRecordComponents.listExpected model S A start fixed stride values).root.reference).1 = some values.length at hc
  rw [← hRoot] at hc
  exact GeneralPaperStoredReadStream.counted_source model A installed _ _ values hc
    (fun index => (GeneralPaperStoredScalarSourceRead.list model S A start fixed stride installed values hRead hRoot index).1)

theorem bits (model : RationalCostModel) (S A start : ℕ) (installed : Installed A) (full : Directory A)
    (hContract : Contract model A installed full) (values : List Bool)
    (hRead : Readback model A installed (GeneralPaperScalarRecordComponents.listExpected model S A start 32 2 (values.map Scalar.bit)))
    (hHeader : GeneralPaperRetainedHeaderCountSources.listHeader model S A start 32 2 (values.map Scalar.bit) ∈ full.headers)
    (hRoot : installed.root = (GeneralPaperScalarRecordComponents.listExpected model S A start 32 2 (values.map Scalar.bit)).root.reference) :
    (GeneralPaperStoredReadStream.bits model A installed).values = some values ∧
      (GeneralPaperStoredReadStream.bits model A installed).count = values.length ∧
      (GeneralPaperStoredReadStream.bits model A installed).work =
        (GeneralPaperHeaderCountReadback.count model A installed installed.root).2 +
        GeneralPaperStoredReadStream.price model A (GeneralPaperStoredScalarRead.bit model A installed 32) (fun _ => 1) 0 values + 128 * (A + 1) := by
  have hc := GeneralPaperRetainedHeaderCountSources.scalar_list model S A start 32 2 installed full hContract
    (values.map Scalar.bit) (by decide) hHeader
  change (GeneralPaperHeaderCountReadback.count model A installed
    (GeneralPaperScalarRecordComponents.listExpected model S A start 32 2 (values.map Scalar.bit)).root.reference).1 = some (values.map Scalar.bit).length at hc
  rw [← hRoot,List.length_map] at hc
  exact GeneralPaperStoredReadStream.counted_source model A installed _ _ values hc
    (fun index => GeneralPaperStoredScalarSourceRead.bit_list model S A start installed values hRead hRoot index)

theorem naturals (model : RationalCostModel) (S A start : ℕ) (installed : Installed A) (full : Directory A)
    (hContract : Contract model A installed full) (values : List ℕ)
    (hRead : Readback model A installed (GeneralPaperScalarRecordComponents.listExpected model S A start 32 1 (values.map Scalar.natural)))
    (hHeader : GeneralPaperRetainedHeaderCountSources.listHeader model S A start 32 1 (values.map Scalar.natural) ∈ full.headers)
    (hRoot : installed.root = (GeneralPaperScalarRecordComponents.listExpected model S A start 32 1 (values.map Scalar.natural)).root.reference) :
    (GeneralPaperStoredReadStream.naturals model A installed 32).values = some values ∧
      (GeneralPaperStoredReadStream.naturals model A installed 32).count = values.length ∧
      (GeneralPaperStoredReadStream.naturals model A installed 32).work =
        (GeneralPaperHeaderCountReadback.count model A installed installed.root).2 +
        GeneralPaperStoredReadStream.price model A (GeneralPaperStoredScalarRead.natural model A installed 32)
          GeneralPaperEncodedScalarStorage.natBits 0 values + 128 * (A + 1) := by
  have hc := GeneralPaperRetainedHeaderCountSources.scalar_list model S A start 32 1 installed full hContract
    (values.map Scalar.natural) (by decide) hHeader
  change (GeneralPaperHeaderCountReadback.count model A installed
    (GeneralPaperScalarRecordComponents.listExpected model S A start 32 1 (values.map Scalar.natural)).root.reference).1 = some (values.map Scalar.natural).length at hc
  rw [← hRoot,List.length_map] at hc
  exact GeneralPaperStoredReadStream.counted_source model A installed _ _ values hc
    (fun index => GeneralPaperStoredScalarSourceRead.natural_list model S A start installed values hRead hRoot index)

theorem rational_array {n : ℕ} (model : RationalCostModel) (S A start : ℕ) (installed : Installed A) (full : Directory A)
    (hContract : Contract model A installed full) (source : FixedArrayTable n ℚ)
    (hRead : Readback model A installed (ofArray (GeneralPaperMappedScalarArrayCursor.expected model S A start (source.data.toList.map Scalar.rational))))
    (hHeader : (GeneralPaperMappedScalarArrayCursor.expected model S A start (source.data.toList.map Scalar.rational)).header ∈ full.headers)
    (hRoot : installed.root = (GeneralPaperMappedScalarArrayCursor.expected model S A start (source.data.toList.map Scalar.rational)).header.region.reference) :
    (GeneralPaperStoredReadStream.rationals model A installed).values = some source.data.toList ∧
      (GeneralPaperStoredReadStream.rationals model A installed).count = n ∧
      (GeneralPaperStoredReadStream.rationals model A installed).work =
        (GeneralPaperHeaderCountReadback.count model A installed installed.root).2 +
        GeneralPaperStoredReadStream.price model A (GeneralPaperStoredScalarRead.rational model A installed 64)
          rationalWordWidth 0 source.data.toList + 128 * (A + 1) := by
  have hc := GeneralPaperRetainedHeaderCountSources.rational_array model S A start installed full hContract source hHeader
  rw [← hRoot] at hc
  have hLength : source.data.toList.length = n := by rw [Array.length_toList,source.size]
  have hr : ∀ index : Fin source.data.toList.length,
      (GeneralPaperStoredScalarRead.rational model A installed 64 index.val).1 = some source.data.toList[index.val] := by
    intro index
    have hi : index.val < n := by simpa only [hLength] using index.isLt
    simpa only [Array.getElem_toList,FixedArrayTable.read] using
      GeneralPaperStoredScalarSourceRead.rational_array model S A start installed source hRead hRoot ⟨index.val,hi⟩
  have h := GeneralPaperStoredReadStream.counted_source model A installed
    (GeneralPaperStoredScalarRead.rational model A installed 64) rationalWordWidth source.data.toList
    (hc.trans (congrArg some hLength.symm)) hr
  simpa only [GeneralPaperStoredReadStream.rationals,hLength] using h

end Blotto.GeneralPaperStoredReadStreamSources
