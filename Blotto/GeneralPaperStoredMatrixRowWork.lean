import Blotto.GeneralPaperStoredReadContext

/-! Only the selected stored matrix row is collected. The enclosing measured
owner derives both outer-index and selected-row capacities; each rational
payload is charged at its own encoding length. -/
namespace Blotto.GeneralPaperStoredMatrixRowWork
open GeneralPaperFieldDirectory GeneralPaperSequentialLayout GeneralPaperReferenceRegionSlots
open GeneralPaperRetainedScalarValue
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperSamplerRecordInstallation (Readback)
open GeneralPaperHeaderCountInstallation (Contract)
open GeneralPaperUnifiedFieldValue
open GeneralPaperMixedReferenceMemory (Word)
open GeneralPaperStoredReadContext (Context)
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192

def bound {m : ℕ} (model : RationalCostModel) (A : ℕ) (row : FixedArrayTable m ℚ) : ℕ :=
  GeneralPaperStoredRationalCollectionWork.bound model A row +
    GeneralPaperStoredReferenceReadWork.readBound model A A + 256 * (A + 1)

theorem bounds {m r : ℕ} (model : RationalCostModel) (S A layoutStart start : ℕ) (plan : GeneralPaperMeasuredBlockPlan.Plan)
    (installed : Installed A) (full : Directory A) (ctx : Context model S A layoutStart plan full installed)
    (table : FixedArrayTable r (FixedArrayTable m ℚ))
    (hRead : Readback model A installed (GeneralPaperMatrixFieldCursor.expected model S A start table))
    (hHeaders : ∀ header ∈ (GeneralPaperMatrixFieldCursor.expected model S A start table).headers,header ∈ full.headers)
    (hRoot : installed.root = (GeneralPaperMatrixFieldCursor.expected model S A start table).root.reference) (index : Fin r) :
    m + 1 < 2 ^ A ∧ (GeneralPaperStoredMatrixRowRead.read model A installed index.val).work ≤ bound model A (table.read index) := by
  have hContract := ctx.contract
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
  have hOuterCount := GeneralPaperStoredReadContext.header_count_fits ctx outer (hHeaders outer hOuterMem)
  have hPointerWork := GeneralPaperStoredReferenceReadWork.read_work model A A 64 index.val _ installed.root child.root.reference
    le_rfl (hOuterIndex.trans hOuterCount) hPointer
  have hRow := GeneralPaperStoredRationalCollectionWork.work_from_owner model S A rowStart
    (GeneralPaperStoredScalarRead.atRoot installed child.root.reference) full hChildContract (table.read index) hChildRead hHeader rfl
    ctx.positive (GeneralPaperStoredReadContext.header_capacity ctx rowFields.header hHeader)
  have hExtent := GeneralPaperStoredStreamWork.rational_array_capacity model S A rowStart (table.read index)
    ctx.positive (GeneralPaperStoredReadContext.header_capacity ctx rowFields.header hHeader)
  refine ⟨hExtent,?_⟩
  rw [(GeneralPaperStoredMatrixRowRead.trace model A installed index.val child.root.reference hPointer).2.2]
  unfold bound
  omega

end Blotto.GeneralPaperStoredMatrixRowWork
