import Blotto.GeneralPaperFieldDirectoryLookup

/-! Indexed matrix reads follow actual outer/row references to the scalar
payload. No source array, decoded target or row directory is a reader input.
Source-index correspondence and local work follow from installed ownership. -/
namespace Blotto.GeneralPaperMatrixFieldRead
open GeneralPaperSequentialLayout GeneralPaperFieldDirectory GeneralPaperReferenceRegionSlots
open GeneralPaperRetainedScalarValue
open GeneralPaperFieldDirectoryInstallation (Installed)
open GeneralPaperMixedReferenceMemory (Word)
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192

def read (model : RationalCostModel) (A : ℕ) (installed : Installed A) (row column : ℕ) : Option Scalar × ℕ :=
  let outer := GeneralPaperMixedReferenceRegionProgram.read model A installed.references installed.root 64 row
  match outer.1 with
  | none => (none,outer.2 + 64 * A + 64)
  | some ⟨B,rowRoot⟩ =>
    let inner := GeneralPaperMixedReferenceRegionProgram.read model B installed.references rowRoot 64 column
    match inner.1 with
    | none => (none,outer.2 + inner.2 + 64 * (A + B + 1))
    | some ⟨C,cellRoot⟩ =>
      let scalar := GeneralPaperPayloadMemory.read C encode installed.payloads cellRoot
      (scalar.1,outer.2 + inner.2 + scalar.2 + 64 * (A + B + C + 1))

def rational (model : RationalCostModel) (A : ℕ) (installed : Installed A) (row column : ℕ) : Option ℚ × ℕ :=
  let actual := read model A installed row column
  match actual.1 with
  | some (.rational value) => (some value,actual.2 + 64 * A + 64)
  | _ => (none,actual.2 + 64 * A + 64)

theorem trace (model : RationalCostModel) (A : ℕ) (installed : Installed A) (row column : ℕ)
    (rowRoot cellRoot : FixedBinaryWord A) (value : Scalar)
    (hOuter : (GeneralPaperMixedReferenceRegionProgram.read model A installed.references installed.root 64 row).1 = some (⟨A,rowRoot⟩ : Word))
    (hInner : (GeneralPaperMixedReferenceRegionProgram.read model A installed.references rowRoot 64 column).1 = some (⟨A,cellRoot⟩ : Word))
    (hScalar : (GeneralPaperPayloadMemory.read A encode installed.payloads cellRoot).1 = some value) :
    (read model A installed row column).1 = some value ∧
      (read model A installed row column).2 =
        (GeneralPaperMixedReferenceRegionProgram.read model A installed.references installed.root 64 row).2 +
        (GeneralPaperMixedReferenceRegionProgram.read model A installed.references rowRoot 64 column).2 + encode value + 256 * A + 128 := by
  change installed.payloads cellRoot.value = some value at hScalar
  simp only [read,hOuter,hInner,GeneralPaperPayloadMemory.read,hScalar,Option.elim_some]
  constructor
  · exact True.intro
  · ring

theorem source {m r : ℕ} (model : RationalCostModel) (S A start : ℕ) (source : FixedArrayTable r (FixedArrayTable m ℚ))
    (hA : 0 < A) (hCap : start + (GeneralPaperEqualMeasuredRetainedPlan.matrix model S A source).sizes.sum < 2 ^ A)
    (i : Fin r) (j : Fin m) :
    let directory := GeneralPaperMatrixFieldCursor.expected model S A start source
    let installed := GeneralPaperFieldDirectoryInstallation.install model S A directory
    ∃ rowRoot : FixedBinaryWord A,(read model A installed i.val j.val).1 = some (.rational ((source.read i).read j)) ∧
      (read model A installed i.val j.val).2 =
        (GeneralPaperMixedReferenceRegionProgram.read model A installed.references installed.root 64 i.val).2 +
        (GeneralPaperMixedReferenceRegionProgram.read model A installed.references rowRoot 64 j.val).2 +
        rationalWordWidth ((source.read i).read j) + 256 * A + 128 := by
  dsimp only
  let plan := GeneralPaperEqualMeasuredRetainedPlan.matrix model S A source
  let directory := GeneralPaperMatrixFieldCursor.expected model S A start source
  let installed := GeneralPaperFieldDirectoryInstallation.install model S A directory
  let rows := source.data.toList
  let next := start + A * (64 + rows.length)
  let dirs := GeneralPaperChildDirectorySpecification.directories (GeneralPaperMatrixFieldCursor.rowSchema model S A)
    (GeneralPaperMatrixFieldCursor.rowExpected model S A) next rows
  have hSafe := (GeneralPaperMatrixFieldCursor.success model S A start source []).2.2
  have hPos := GeneralPaperEqualMeasuredPlanPositive.matrix model S A source hA
  have hIndex : i.val < rows.length := by dsimp only [rows]; rw [Array.length_toList,source.size]; exact i.isLt
  have hDirLength : dirs.length = rows.length := GeneralPaperChildDirectorySpecification.directory_count _ _ _ _
  have hDirIndex : i.val < dirs.length := by rw [hDirLength]; exact hIndex
  obtain ⟨rowStart,hLookup⟩ := GeneralPaperFieldDirectoryLookup.child_lookup
    (GeneralPaperMatrixFieldCursor.rowSchema model S A) (GeneralPaperMatrixFieldCursor.rowExpected model S A) next rows i.val hIndex
  have hRowValue : rows[i.val] = source.read i := by simp only [rows,Array.getElem_toList,FixedArrayTable.read]
  rw [hRowValue,List.getElem?_eq_getElem hDirIndex] at hLookup
  have hDirEq := Option.some.inj hLookup
  let row := source.read i
  let rowDirectory := GeneralPaperMatrixFieldCursor.rowExpected model S A row rowStart
  let rowFields := GeneralPaperMappedScalarArrayCursor.expected model S A rowStart (row.data.toList.map Scalar.rational)
  change dirs[i.val] = rowDirectory at hDirEq
  have hDirectoryMem : rowDirectory ∈ dirs := by
    rw [← hDirEq]
    exact List.getElem_mem hDirIndex
  let outerHeader : Header A := ⟨GeneralPaperScalarArrayFieldCursor.layoutHeader A start rows.length,64,
    (dirs.map Directory.root).map Region.reference⟩
  have hOuterMem : outerHeader ∈ directory.headers := List.mem_cons_self ..
  have hOuterIndex : i.val < outerHeader.targets.length := by
    change i.val < ((dirs.map Directory.root).map Region.reference).length
    rw [List.length_map,List.length_map,hDirLength]
    exact hIndex
  have hOuter := GeneralPaperFieldDirectoryInstallation.header_read model S A start plan directory hSafe hA hCap outerHeader hOuterMem
    ⟨i.val,hOuterIndex⟩
  dsimp only [outerHeader] at hOuter
  simp only [List.getElem_map] at hOuter
  rw [hDirEq] at hOuter
  change (GeneralPaperMixedReferenceRegionProgram.read model A installed.references installed.root 64 i.val).1 =
    some (⟨A,rowDirectory.root.reference⟩ : Word) at hOuter
  have hRowHeaderMem : rowFields.header ∈ directory.headers :=
    List.mem_cons_of_mem outerHeader (GeneralPaperFieldDirectoryLookup.collect_header_member dirs rowDirectory hDirectoryMem
      rowFields.header (List.mem_cons_self ..))
  have hColumnIndex : j.val < (row.data.toList.map Scalar.rational).length := by
    rw [List.length_map,Array.length_toList,row.size]
    exact j.isLt
  have hRowHeaderIndex : j.val < rowFields.header.targets.length := by
    rw [GeneralPaperFieldDirectoryLookup.array_target_count]
    exact hColumnIndex
  obtain ⟨cell,hCell,hTarget,hValue⟩ := GeneralPaperFieldDirectoryLookup.array_cell model S A rowStart
    (row.data.toList.map Scalar.rational) j.val hColumnIndex
  rw [List.getElem?_eq_getElem hRowHeaderIndex] at hTarget
  have hTargetEq := Option.some.inj hTarget
  have hInner := GeneralPaperFieldDirectoryInstallation.header_read model S A start plan directory hSafe hA hCap rowFields.header hRowHeaderMem
    ⟨j.val,hRowHeaderIndex⟩
  rw [hTargetEq] at hInner
  change (GeneralPaperMixedReferenceRegionProgram.read model A installed.references rowDirectory.root.reference 64 j.val).1 =
    some (⟨A,cell.region.reference⟩ : Word) at hInner
  have hCellGlobal : cell ∈ directory.cells :=
    GeneralPaperFieldDirectoryLookup.collect_cell_member dirs rowDirectory hDirectoryMem cell hCell
  have hScalar := (GeneralPaperFieldDirectoryInstallation.scalar_read model S A start plan directory hSafe hPos hCap cell hCellGlobal).1
  have hOriginal : cell.value = Scalar.rational ((source.read i).read j) := by
    simpa only [row,List.getElem_map,Array.getElem_toList,FixedArrayTable.read] using hValue
  rw [hOriginal] at hScalar
  exact ⟨rowDirectory.root.reference,trace model A installed i.val j.val rowDirectory.root.reference cell.region.reference
    (.rational ((source.read i).read j)) hOuter hInner hScalar⟩

theorem rational_source {m r : ℕ} (model : RationalCostModel) (S A start : ℕ) (source : FixedArrayTable r (FixedArrayTable m ℚ))
    (hA : 0 < A) (hCap : start + (GeneralPaperEqualMeasuredRetainedPlan.matrix model S A source).sizes.sum < 2 ^ A)
    (i : Fin r) (j : Fin m) :
    (rational model A (GeneralPaperFieldDirectoryInstallation.install model S A
      (GeneralPaperMatrixFieldCursor.expected model S A start source)) i.val j.val).1 = some ((source.read i).read j) := by
  obtain ⟨_,hRead,_⟩ := GeneralPaperMatrixFieldRead.source model S A start source hA hCap i j
  simp only [rational,hRead]

end Blotto.GeneralPaperMatrixFieldRead
