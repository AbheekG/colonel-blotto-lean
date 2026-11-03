import Blotto.GeneralPaperRouteFieldCursor

/-! A record-field reader follows its stored root slot into the scalar cell.
Both read views come from one address map. Data and local prices depend only
on the returned memory/root, the field index and the cost model. -/
namespace Blotto.GeneralPaperRecordScalarRead
open GeneralPaperSequentialLayout GeneralPaperRetainedScalarValue GeneralPaperFieldDirectory
open GeneralPaperUnifiedFieldValue
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperMixedReferenceMemory (Word)
open GeneralPaperScalarFieldCursor (Cell)
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 8192

def read (model : RationalCostModel) (A : ℕ) (installed : Installed A) (index : ℕ) : Option Scalar × ℕ :=
  let pointer := GeneralPaperMixedReferenceRegionProgram.read model A (referenceMemory installed.memory) installed.root 0 index
  match pointer.1 with
  | none => (none,pointer.2 + 64 * A + 64)
  | some ⟨B,root⟩ =>
    let payload := GeneralPaperPayloadMemory.read B GeneralPaperRetainedScalarValue.encode (scalarMemory installed.memory) root
    (payload.1,pointer.2 + payload.2 + 64 * (A + B + 1))

theorem trace (model : RationalCostModel) (A : ℕ) (installed : Installed A) (index : ℕ)
    (root : FixedBinaryWord A) (value : Scalar)
    (hPointer : (GeneralPaperMixedReferenceRegionProgram.read model A (referenceMemory installed.memory) installed.root 0 index).1 =
      some (⟨A,root⟩ : Word))
    (hScalar : (GeneralPaperPayloadMemory.read A GeneralPaperRetainedScalarValue.encode (scalarMemory installed.memory) root).1 = some value) :
    (read model A installed index).1 = some value ∧ (read model A installed index).2 =
      (GeneralPaperMixedReferenceRegionProgram.read model A (referenceMemory installed.memory) installed.root 0 index).2 +
      GeneralPaperRetainedScalarValue.encode value + 192 * A + 128 := by
  change scalarMemory installed.memory root.value = some value at hScalar
  simp only [read,hPointer,GeneralPaperPayloadMemory.read,hScalar,Option.elim_some]
  constructor
  · exact True.intro
  · ring

theorem cell_lookup (A : ℕ) (cells : List (Cell A)) (values : List Scalar)
    (hValues : cells.map Cell.value = values) (index : Fin values.length) :
    ∃ cell ∈ cells,(cells.map (fun cell => cell.region.reference))[index.val]? = some cell.region.reference ∧
      cell.value = values[index.val] := by
  have hLength := congrArg List.length hValues
  simp only [List.length_map] at hLength
  have hIndex : index.val < cells.length := by rw [hLength]; exact index.isLt
  refine ⟨cells[index.val],List.getElem_mem hIndex,?_,?_⟩
  · simp only [List.getElem?_map,List.getElem?_eq_getElem hIndex,Option.map_some]
  · have h := congrArg (fun list => list[index.val]?) hValues
    simpa only [List.getElem?_map,List.getElem?_eq_getElem hIndex,List.getElem?_eq_getElem index.isLt,
      Option.map_some,Option.some.injEq] using h

theorem expected_values (model : RationalCostModel) (S A start arity : ℕ) (values : List Scalar) :
    (GeneralPaperTrailingScalarRecord.expected model S A start arity values).cells.map Cell.value = values := by
  exact GeneralPaperScalarFieldCursor.cells_values A _ values (by rw [GeneralPaperSequentialLayout.count,List.length_map])

theorem field_at (model : RationalCostModel) (S A start : ℕ) (plan : GeneralPaperMeasuredBlockPlan.Plan)
    (directory : Directory A)
    (hSafe : GeneralPaperFieldDirectorySafety.Safe (GeneralPaperMeasuredBlockLayout.run model S A start plan).1 directory)
    (hCovered : GeneralPaperFieldDirectoryPartition.Covered (GeneralPaperMeasuredBlockLayout.run model S A start plan).1 directory)
    (hPos : GeneralPaperMeasuredPlanPositive.Positive plan) (hA : 0 < A) (hCap : start + plan.sizes.sum < 2 ^ A)
    (header : GeneralPaperReferenceRegionSlots.Header A) (hHeader : header ∈ directory.headers) (hFixed : header.fixed = 0)
    (cell : Cell A) (hCell : cell ∈ directory.cells) (index : Fin header.targets.length)
    (hTarget : header.targets[index.val] = cell.region.reference) :
    let installed := GeneralPaperUnifiedDirectoryInstallation.install model S A directory
    let atRecord : Installed A := ⟨installed.memory,header.region.reference,installed.work⟩
    (read model A atRecord index.val).1 = some cell.value ∧ (read model A atRecord index.val).2 =
      (GeneralPaperMixedReferenceRegionProgram.read model A (referenceMemory atRecord.memory) atRecord.root 0 index.val).2 +
      GeneralPaperRetainedScalarValue.encode cell.value + 192 * A + 128 := by
  dsimp only
  have hPointer := GeneralPaperUnifiedDirectoryInstallation.header_read model S A start plan directory hSafe hCovered hA hCap
    header hHeader index
  rw [hFixed,hTarget] at hPointer
  have hScalar := GeneralPaperUnifiedDirectoryInstallation.scalar_read model S A start plan directory hSafe hPos hCap cell hCell
  exact trace model A _ index.val cell.region.reference cell.value hPointer hScalar

theorem route_field {m : ℕ} (model : RationalCostModel) (S A start : ℕ) (source : GroupRoute m) (hA : 0 < A)
    (hCap : start + (GeneralPaperEqualMeasuredLeafPlans.route model S A source).sizes.sum < 2 ^ A)
    (index : Fin (GeneralPaperRouteFieldCursor.values source).length) :
    let installed := GeneralPaperUnifiedDirectoryInstallation.install model S A (GeneralPaperRouteFieldCursor.expected model S A source start)
    (read model A installed index.val).1 = some ((GeneralPaperRouteFieldCursor.values source)[index.val]) ∧
      (read model A installed index.val).2 =
        (GeneralPaperMixedReferenceRegionProgram.read model A (referenceMemory installed.memory) installed.root 0 index.val).2 +
        GeneralPaperRetainedScalarValue.encode ((GeneralPaperRouteFieldCursor.values source)[index.val]) + 192 * A + 128 := by
  dsimp only
  let plan := GeneralPaperEqualMeasuredLeafPlans.route model S A source
  let directory := GeneralPaperRouteFieldCursor.expected model S A source start
  obtain ⟨_,_,hSafe,hCovered⟩ := GeneralPaperRouteFieldCursor.success model S A start source []
  obtain ⟨cell,hCell,hTarget,hValue⟩ := cell_lookup A directory.cells (GeneralPaperRouteFieldCursor.values source)
    (expected_values model S A start 16 (GeneralPaperRouteFieldCursor.values source)) index
  have hCount := congrArg List.length (expected_values model S A start 16 (GeneralPaperRouteFieldCursor.values source))
  simp only [List.length_map] at hCount
  change directory.cells.length = (GeneralPaperRouteFieldCursor.values source).length at hCount
  let header : GeneralPaperReferenceRegionSlots.Header A := ⟨directory.root,0,directory.cells.map (fun cell => cell.region.reference)⟩
  have hHeader : header ∈ directory.headers := List.mem_singleton_self _
  have hIndex : index.val < header.targets.length := by
    change index.val < (directory.cells.map (fun cell => cell.region.reference)).length
    rw [List.length_map,hCount]
    exact index.isLt
  have hPointer := GeneralPaperUnifiedDirectoryInstallation.header_read model S A start plan directory hSafe hCovered hA hCap
    header hHeader ⟨index.val,hIndex⟩
  rw [List.getElem?_eq_getElem hIndex] at hTarget
  have hTargetEq := Option.some.inj hTarget
  change header.targets[index.val] = cell.region.reference at hTargetEq
  rw [hTargetEq] at hPointer
  have hScalar := GeneralPaperUnifiedDirectoryInstallation.scalar_read model S A start plan directory hSafe
    (GeneralPaperEqualMeasuredPlanPositive.route model S A source hA) hCap cell hCell
  have h := trace model A (GeneralPaperUnifiedDirectoryInstallation.install model S A directory)
    index.val cell.region.reference cell.value hPointer hScalar
  rw [hValue] at h
  exact h

end Blotto.GeneralPaperRecordScalarRead
