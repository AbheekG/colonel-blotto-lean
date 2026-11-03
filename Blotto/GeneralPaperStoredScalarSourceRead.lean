import Blotto.GeneralPaperStoredScalarRead

/-! Source correspondence is parameterized by readback of the current memory,
so it applies inside a larger installed sampler. No isolated installation or
source value is a reader input. Array and control/bit-list prefixes are fixed. -/
namespace Blotto.GeneralPaperStoredScalarSourceRead
open GeneralPaperFieldDirectory GeneralPaperSequentialLayout GeneralPaperReferenceRegionSlots GeneralPaperRetainedScalarValue
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperSamplerRecordInstallation (Readback)
open GeneralPaperUnifiedFieldValue
open GeneralPaperScalarFieldCursor (Cell)
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 8192

theorem fields (model : RationalCostModel) (A : ℕ) (installed : Installed A) (directory : Directory A)
    (hRead : Readback model A installed directory) (header : Header A) (hHeader : header ∈ directory.headers)
    (cells : List (Cell A)) (values : List Scalar) (hCells : ∀ cell ∈ cells,cell ∈ directory.cells)
    (hTargets : header.targets = cells.map (fun cell => cell.region.reference)) (hValues : cells.map Cell.value = values)
    (hRoot : installed.root = header.region.reference) (index : Fin values.length) :
    (GeneralPaperStoredScalarRead.read model A installed header.fixed index.val).1 = some values[index.val] ∧
      (GeneralPaperStoredScalarRead.read model A installed header.fixed index.val).2 =
        (GeneralPaperMixedReferenceRegionProgram.read model A (referenceMemory installed.memory) installed.root header.fixed index.val).2 +
        GeneralPaperRetainedScalarValue.encode values[index.val] + 192 * A + 128 := by
  obtain ⟨cell,hCell,hTarget,hValue⟩ := GeneralPaperRecordScalarRead.cell_lookup A cells values hValues index
  have hCount := congrArg List.length hValues
  simp only [List.length_map] at hCount
  have hIndex : index.val < header.targets.length := by rw [hTargets,List.length_map,hCount]; exact index.isLt
  rw [← hTargets,List.getElem?_eq_getElem hIndex] at hTarget
  have h := GeneralPaperStoredScalarRead.from_readback model A installed directory hRead header hHeader cell (hCells cell hCell)
    ⟨index.val,hIndex⟩ (Option.some.inj hTarget)
  rw [GeneralPaperStoredScalarRead.read_ext model A (GeneralPaperStoredScalarRead.atRoot installed header.region.reference)
    installed rfl hRoot.symm,hValue,← hRoot] at h
  exact h

theorem array (model : RationalCostModel) (S A start : ℕ) (installed : Installed A) (values : List Scalar)
    (hRead : Readback model A installed (ofArray (GeneralPaperMappedScalarArrayCursor.expected model S A start values)))
    (hRoot : installed.root = (GeneralPaperMappedScalarArrayCursor.expected model S A start values).header.region.reference)
    (index : Fin values.length) :
    (GeneralPaperStoredScalarRead.read model A installed 64 index.val).1 = some values[index.val] ∧
      (GeneralPaperStoredScalarRead.read model A installed 64 index.val).2 =
        (GeneralPaperMixedReferenceRegionProgram.read model A (referenceMemory installed.memory) installed.root 64 index.val).2 +
        GeneralPaperRetainedScalarValue.encode values[index.val] + 192 * A + 128 := by
  let regions := (GeneralPaperSequentialLayout.run model S A (start + A * (64 + values.length)) (values.map GeneralPaperRetainedScalarValue.encode)).1
  have hValues := GeneralPaperScalarFieldCursor.cells_values A regions values (by dsimp only [regions]; rw [GeneralPaperSequentialLayout.count,List.length_map])
  exact fields model A installed _ hRead _ (List.mem_singleton_self _)
    (GeneralPaperMappedScalarArrayCursor.expected model S A start values).cells values (fun _ hc => hc) rfl hValues hRoot index

theorem list (model : RationalCostModel) (S A start fixed stride : ℕ) (installed : Installed A) (values : List Scalar)
    (hRead : Readback model A installed (GeneralPaperScalarRecordComponents.listExpected model S A start fixed stride values))
    (hRoot : installed.root = (GeneralPaperScalarRecordComponents.listExpected model S A start fixed stride values).root.reference)
    (index : Fin values.length) :
    (GeneralPaperStoredScalarRead.read model A installed fixed index.val).1 = some values[index.val] ∧
      (GeneralPaperStoredScalarRead.read model A installed fixed index.val).2 =
        (GeneralPaperMixedReferenceRegionProgram.read model A (referenceMemory installed.memory) installed.root fixed index.val).2 +
        GeneralPaperRetainedScalarValue.encode values[index.val] + 192 * A + 128 := by
  let regions := (GeneralPaperSequentialLayout.run model S A (start + A * (stride * values.length + fixed)) (values.map GeneralPaperRetainedScalarValue.encode)).1
  have hValues := GeneralPaperScalarFieldCursor.cells_values A regions values (by dsimp only [regions]; rw [GeneralPaperSequentialLayout.count,List.length_map])
  exact fields model A installed _ hRead (GeneralPaperRetainedHeaderCountSources.listHeader model S A start fixed stride values)
    (List.mem_singleton_self _) _ values (fun _ hc => hc) rfl hValues hRoot index

theorem rational_array {n : ℕ} (model : RationalCostModel) (S A start : ℕ) (installed : Installed A) (source : FixedArrayTable n ℚ)
    (hRead : Readback model A installed (ofArray (GeneralPaperMappedScalarArrayCursor.expected model S A start (source.data.toList.map Scalar.rational))))
    (hRoot : installed.root = (GeneralPaperMappedScalarArrayCursor.expected model S A start (source.data.toList.map Scalar.rational)).header.region.reference)
    (index : Fin n) :
    (GeneralPaperStoredScalarRead.rational model A installed 64 index.val).1 = some (source.read index) := by
  have h := (array model S A start installed (source.data.toList.map Scalar.rational) hRead hRoot
    ⟨index.val,by rw [List.length_map,Array.length_toList,source.size]; exact index.isLt⟩).1
  have hs : (GeneralPaperStoredScalarRead.read model A installed 64 index.val).1 = some (.rational (source.read index)) := by
    simpa only [List.getElem_map,Array.getElem_toList,FixedArrayTable.read] using h
  exact (GeneralPaperStoredScalarRead.rational_of_scalar model A installed 64 index.val _ hs).1

theorem natural_array {n : ℕ} (model : RationalCostModel) (S A start : ℕ) (installed : Installed A) (source : FixedArrayTable n ℕ)
    (hRead : Readback model A installed (ofArray (GeneralPaperMappedScalarArrayCursor.expected model S A start (source.data.toList.map Scalar.natural))))
    (hRoot : installed.root = (GeneralPaperMappedScalarArrayCursor.expected model S A start (source.data.toList.map Scalar.natural)).header.region.reference)
    (index : Fin n) :
    (GeneralPaperStoredScalarRead.natural model A installed 64 index.val).1 = some (source.read index) := by
  have h := (array model S A start installed (source.data.toList.map Scalar.natural) hRead hRoot
    ⟨index.val,by rw [List.length_map,Array.length_toList,source.size]; exact index.isLt⟩).1
  have hs : (GeneralPaperStoredScalarRead.read model A installed 64 index.val).1 = some (.natural (source.read index)) := by
    simpa only [List.getElem_map,Array.getElem_toList,FixedArrayTable.read] using h
  exact (GeneralPaperStoredScalarRead.natural_of_scalar model A installed 64 index.val _ hs).1

theorem natural_list (model : RationalCostModel) (S A start : ℕ) (installed : Installed A) (values : List ℕ)
    (hRead : Readback model A installed (GeneralPaperScalarRecordComponents.listExpected model S A start 32 1 (values.map Scalar.natural)))
    (hRoot : installed.root = (GeneralPaperScalarRecordComponents.listExpected model S A start 32 1 (values.map Scalar.natural)).root.reference)
    (index : Fin values.length) :
    (GeneralPaperStoredScalarRead.natural model A installed 32 index.val).1 = some values[index.val] := by
  have h := (list model S A start 32 1 installed (values.map Scalar.natural) hRead hRoot
    ⟨index.val,by rw [List.length_map]; exact index.isLt⟩).1
  have hs : (GeneralPaperStoredScalarRead.read model A installed 32 index.val).1 = some (.natural values[index.val]) := by
    simpa only [List.getElem_map] using h
  exact (GeneralPaperStoredScalarRead.natural_of_scalar model A installed 32 index.val _ hs).1

theorem bit_list (model : RationalCostModel) (S A start : ℕ) (installed : Installed A) (values : List Bool)
    (hRead : Readback model A installed (GeneralPaperScalarRecordComponents.listExpected model S A start 32 2 (values.map Scalar.bit)))
    (hRoot : installed.root = (GeneralPaperScalarRecordComponents.listExpected model S A start 32 2 (values.map Scalar.bit)).root.reference)
    (index : Fin values.length) :
    (GeneralPaperStoredScalarRead.bit model A installed 32 index.val).1 = some values[index.val] := by
  have h := (list model S A start 32 2 installed (values.map Scalar.bit) hRead hRoot
    ⟨index.val,by rw [List.length_map]; exact index.isLt⟩).1
  have hs : (GeneralPaperStoredScalarRead.read model A installed 32 index.val).1 = some (.bit values[index.val]) := by
    simpa only [List.getElem_map] using h
  exact (GeneralPaperStoredScalarRead.bit_of_scalar model A installed 32 index.val _ hs).1

end Blotto.GeneralPaperStoredScalarSourceRead
