import Blotto.GeneralPaperStoredBooleanWordSourceRead

/-! Read just the selected endpoint row. The outer reference and inner stored
count determine the actual reader; other cached rows are not traversed. -/
namespace Blotto.GeneralPaperStoredMatrixRowRead
open GeneralPaperFieldDirectory GeneralPaperSequentialLayout GeneralPaperReferenceRegionSlots
open GeneralPaperRetainedScalarValue
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperSamplerRecordInstallation (Readback)
open GeneralPaperHeaderCountInstallation (Contract)
open GeneralPaperUnifiedFieldValue
open GeneralPaperMixedReferenceMemory (Word)
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 8192

def read (model : RationalCostModel) (A : ℕ) (installed : Installed A) (index : ℕ) : GeneralPaperStoredReadStream.Result ℚ :=
  let pointer := GeneralPaperMixedReferenceRegionProgram.read model A (referenceMemory installed.memory) installed.root 64 index
  match pointer.1 with
  | none => ⟨none,0,pointer.2 + 64 * (A + 1)⟩
  | some ⟨B,root⟩ =>
    let actual := GeneralPaperStoredReadStream.rationals model B (GeneralPaperStoredScalarRead.atRoot installed root)
    ⟨actual.values,actual.count,pointer.2 + actual.work + 64 * (A + B + 1)⟩

theorem trace (model : RationalCostModel) (A : ℕ) (installed : Installed A) (index : ℕ) (root : FixedBinaryWord A)
    (hPointer : (GeneralPaperMixedReferenceRegionProgram.read model A (referenceMemory installed.memory) installed.root 64 index).1 =
      some (⟨A,root⟩ : Word)) :
    (read model A installed index).values = (GeneralPaperStoredReadStream.rationals model A (GeneralPaperStoredScalarRead.atRoot installed root)).values ∧
      (read model A installed index).count = (GeneralPaperStoredReadStream.rationals model A (GeneralPaperStoredScalarRead.atRoot installed root)).count ∧
      (read model A installed index).work =
        (GeneralPaperMixedReferenceRegionProgram.read model A (referenceMemory installed.memory) installed.root 64 index).2 +
        (GeneralPaperStoredReadStream.rationals model A (GeneralPaperStoredScalarRead.atRoot installed root)).work + 128 * A + 64 := by
  simp only [read,hPointer]
  refine ⟨True.intro,True.intro,?_⟩
  ring

theorem source {m r : ℕ} (model : RationalCostModel) (S A start : ℕ) (installed : Installed A)
    (full : Directory A) (hContract : Contract model A installed full) (table : FixedArrayTable r (FixedArrayTable m ℚ))
    (hRead : Readback model A installed (GeneralPaperMatrixFieldCursor.expected model S A start table))
    (hHeaders : ∀ header ∈ (GeneralPaperMatrixFieldCursor.expected model S A start table).headers,header ∈ full.headers)
    (hRoot : installed.root = (GeneralPaperMatrixFieldCursor.expected model S A start table).root.reference) (index : Fin r) :
    ∃ rowRoot : FixedBinaryWord A,
      (read model A installed index.val).values = some (table.read index).data.toList ∧
      (read model A installed index.val).count = m ∧
      (read model A installed index.val).work =
        (GeneralPaperMixedReferenceRegionProgram.read model A (referenceMemory installed.memory) installed.root 64 index.val).2 +
        (GeneralPaperStoredReadStream.rationals model A (GeneralPaperStoredScalarRead.atRoot installed rowRoot)).work + 128 * A + 64 := by
  let directory := GeneralPaperMatrixFieldCursor.expected model S A start table
  let rows := table.data.toList
  let next := start + A * (64 + rows.length)
  let dirs := GeneralPaperChildDirectorySpecification.directories (GeneralPaperMatrixFieldCursor.rowSchema model S A)
    (GeneralPaperMatrixFieldCursor.rowExpected model S A) next rows
  have hIndex : index.val < rows.length := by dsimp only [rows]; rw [Array.length_toList,table.size]; exact index.isLt
  have hDirLength : dirs.length = rows.length := GeneralPaperChildDirectorySpecification.directory_count _ _ _ _
  have hDirIndex : index.val < dirs.length := by rw [hDirLength]; exact hIndex
  obtain ⟨rowStart,hLookup⟩ := GeneralPaperFieldDirectoryLookup.child_lookup
    (GeneralPaperMatrixFieldCursor.rowSchema model S A) (GeneralPaperMatrixFieldCursor.rowExpected model S A) next rows index.val hIndex
  have hRowValue : rows[index.val] = table.read index := by simp only [rows,Array.getElem_toList,FixedArrayTable.read]
  rw [hRowValue,List.getElem?_eq_getElem hDirIndex] at hLookup
  have hDirEq := Option.some.inj hLookup
  let child := GeneralPaperMatrixFieldCursor.rowExpected model S A (table.read index) rowStart
  let rowFields := GeneralPaperMappedScalarArrayCursor.expected model S A rowStart ((table.read index).data.toList.map Scalar.rational)
  change dirs[index.val] = child at hDirEq
  have hChildMem : child ∈ dirs := by rw [← hDirEq]; exact List.getElem_mem hDirIndex
  let outer : Header A := ⟨GeneralPaperScalarArrayFieldCursor.layoutHeader A start rows.length,64,
    (dirs.map Directory.root).map Region.reference⟩
  have hOuterMem : outer ∈ directory.headers := List.mem_cons_self ..
  have hOuterIndex : index.val < outer.targets.length := by
    change index.val < ((dirs.map Directory.root).map Region.reference).length
    rw [List.length_map,List.length_map,hDirLength]
    exact hIndex
  have hPointer := hRead.1 outer hOuterMem ⟨index.val,hOuterIndex⟩
  dsimp only [outer] at hPointer
  simp only [List.getElem_map] at hPointer
  rw [hDirEq] at hPointer
  change (GeneralPaperMixedReferenceRegionProgram.read model A (referenceMemory installed.memory) directory.root.reference 64 index.val).1 =
    some (⟨A,child.root.reference⟩ : Word) at hPointer
  rw [← hRoot] at hPointer
  have hChildHeaders : ∀ header ∈ child.headers,header ∈ directory.headers := by
    intro header hh
    exact List.mem_cons_of_mem outer (GeneralPaperFieldDirectoryLookup.collect_header_member dirs child hChildMem header hh)
  have hChildCells : ∀ cell ∈ child.cells,cell ∈ directory.cells := by
    intro cell hc
    exact GeneralPaperFieldDirectoryLookup.collect_cell_member dirs child hChildMem cell hc
  have hChildRead : Readback model A (GeneralPaperStoredScalarRead.atRoot installed child.root.reference) child :=
    GeneralPaperHeaderCountReadback.restrict model A installed directory child hRead hChildHeaders hChildCells
  have hChildContract : Contract model A (GeneralPaperStoredScalarRead.atRoot installed child.root.reference) full := hContract
  have hHeader : rowFields.header ∈ full.headers :=
    hHeaders _ (hChildHeaders _ (List.mem_cons_self ..))
  have hRow := GeneralPaperStoredReadStreamSources.rational_array model S A rowStart
    (GeneralPaperStoredScalarRead.atRoot installed child.root.reference) full hChildContract (table.read index) hChildRead hHeader rfl
  obtain ⟨hv,hc,hw⟩ := trace model A installed index.val child.root.reference hPointer
  exact ⟨child.root.reference,hv.trans hRow.1,hc.trans hRow.2.1,hw⟩

end Blotto.GeneralPaperStoredMatrixRowRead
