import Blotto.GeneralPaperRouteArrayCursor

/-! Source-indexed route access through the one installed array memory.
The outer slot yields the actual record root; the route decoder reads its
stored flag/label/coefficient. All owners and capacities come from layout. -/
namespace Blotto.GeneralPaperRouteArrayRead
open GeneralPaperSequentialLayout GeneralPaperFieldDirectory GeneralPaperReferenceRegionSlots
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperUnifiedFieldValue
open GeneralPaperMixedReferenceMemory (Word)
open GeneralPaperScalarFieldCursor (Cell)
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 8192

def read (model : RationalCostModel) (A : ℕ) (installed : Installed A) (index : ℕ) : Option (Option ℕ × ℚ) × ℕ :=
  let pointer := GeneralPaperMixedReferenceRegionProgram.read model A (referenceMemory installed.memory) installed.root 64 index
  match pointer.1 with
  | none => (none,pointer.2 + 64 * A + 64)
  | some ⟨B,root⟩ =>
    let route := GeneralPaperRouteFieldRead.read model B ⟨installed.memory,root,0⟩
    (route.1,pointer.2 + route.2 + 64 * (A + B + 1))

theorem trace (model : RationalCostModel) (A : ℕ) (installed : Installed A) (index : ℕ) (root : FixedBinaryWord A)
    (value : Option ℕ × ℚ)
    (hPointer : (GeneralPaperMixedReferenceRegionProgram.read model A (referenceMemory installed.memory) installed.root 64 index).1 = some (⟨A,root⟩ : Word))
    (hRoute : (GeneralPaperRouteFieldRead.read model A ⟨installed.memory,root,0⟩).1 = some value) :
    (read model A installed index).1 = some value ∧ (read model A installed index).2 =
      (GeneralPaperMixedReferenceRegionProgram.read model A (referenceMemory installed.memory) installed.root 64 index).2 +
      (GeneralPaperRouteFieldRead.read model A ⟨installed.memory,root,0⟩).2 + 128 * A + 64 := by
  simp only [read,hPointer,hRoute]
  constructor
  · exact True.intro
  · ring

theorem source {n m : ℕ} (model : RationalCostModel) (S A start : ℕ) (source : FixedArrayTable n (GroupRoute m))
    (hA : 0 < A)
    (hCap : start + (GeneralPaperMeasuredArrayBlockPlan.array model S A (GeneralPaperEqualMeasuredLeafPlans.route model S A) source).sizes.sum < 2 ^ A)
    (i : Fin n) :
    let installed := GeneralPaperUnifiedDirectoryInstallation.install model S A (GeneralPaperRouteArrayCursor.expected model S A start source)
    ∃ routeRoot : FixedBinaryWord A,
      (read model A installed i.val).1 = some ((source.read i).1.map Fin.val,(source.read i).2) ∧
      (read model A installed i.val).2 =
        (GeneralPaperMixedReferenceRegionProgram.read model A (referenceMemory installed.memory) installed.root 64 i.val).2 +
        (GeneralPaperRouteFieldRead.read model A ⟨installed.memory,routeRoot,0⟩).2 + 128 * A + 64 := by
  dsimp only
  let plan := GeneralPaperMeasuredArrayBlockPlan.array model S A (GeneralPaperEqualMeasuredLeafPlans.route model S A) source
  let directory := GeneralPaperRouteArrayCursor.expected model S A start source
  let installed := GeneralPaperUnifiedDirectoryInstallation.install model S A directory
  let routes := source.data.toList
  let dirs := GeneralPaperChildDirectorySpecification.directories (GeneralPaperRouteArrayCursor.schema model S A)
    (GeneralPaperRouteFieldCursor.expected model S A) (start + A * (64 + routes.length)) routes
  have hSafe := (GeneralPaperRouteArrayCursor.success model S A start source []).2.2
  have hCovered := GeneralPaperRouteArrayCursor.covered model S A start source
  have hPos := GeneralPaperMeasuredPlanPositive.array model S A (GeneralPaperEqualMeasuredLeafPlans.route model S A) source hA
    (fun j => GeneralPaperEqualMeasuredPlanPositive.route model S A (source.read j) hA)
  have hIndex : i.val < routes.length := by dsimp only [routes]; rw [Array.length_toList,source.size]; exact i.isLt
  have hCount : dirs.length = routes.length := GeneralPaperChildDirectorySpecification.directory_count _ _ _ _
  have hDirIndex : i.val < dirs.length := by rw [hCount]; exact hIndex
  obtain ⟨routeStart,hLookup⟩ := GeneralPaperFieldDirectoryLookup.child_lookup (GeneralPaperRouteArrayCursor.schema model S A)
    (GeneralPaperRouteFieldCursor.expected model S A) (start + A * (64 + routes.length)) routes i.val hIndex
  have hSource : routes[i.val] = source.read i := by simp only [routes,Array.getElem_toList,FixedArrayTable.read]
  rw [hSource,List.getElem?_eq_getElem hDirIndex] at hLookup
  have hDirEq := Option.some.inj hLookup
  let route := source.read i
  let routeDir := GeneralPaperRouteFieldCursor.expected model S A route routeStart
  change dirs[i.val] = routeDir at hDirEq
  have hRouteMem : routeDir ∈ dirs := by rw [← hDirEq]; exact List.getElem_mem hDirIndex
  let outer : Header A := ⟨GeneralPaperScalarArrayFieldCursor.layoutHeader A start routes.length,64,
    (dirs.map Directory.root).map Region.reference⟩
  have hOuterMem : outer ∈ directory.headers := List.mem_cons_self ..
  have hOuterIndex : i.val < outer.targets.length := by
    change i.val < ((dirs.map Directory.root).map Region.reference).length
    rw [List.length_map,List.length_map,hCount]
    exact hIndex
  have hPointer := GeneralPaperUnifiedDirectoryInstallation.header_read model S A start plan directory hSafe hCovered hA hCap
    outer hOuterMem ⟨i.val,hOuterIndex⟩
  dsimp only [outer] at hPointer
  simp only [List.getElem_map] at hPointer
  rw [hDirEq] at hPointer
  change (GeneralPaperMixedReferenceRegionProgram.read model A (referenceMemory installed.memory) installed.root 64 i.val).1 =
    some (⟨A,routeDir.root.reference⟩ : Word) at hPointer
  have hDecoded : (GeneralPaperRouteFieldRead.read model A ⟨installed.memory,routeDir.root.reference,0⟩).1 =
      some (route.1.map Fin.val,route.2) := by
    apply GeneralPaperRouteFieldRead.source_of_fields model A _ route
    intro field
    have hValues := GeneralPaperRecordScalarRead.expected_values model S A routeStart 16 (GeneralPaperRouteFieldCursor.values route)
    change routeDir.cells.map Cell.value = GeneralPaperRouteFieldCursor.values route at hValues
    obtain ⟨cell,hCell,hTarget,hValue⟩ := GeneralPaperRecordScalarRead.cell_lookup A routeDir.cells _ hValues field
    let header : Header A := ⟨routeDir.root,0,routeDir.cells.map (fun cell => cell.region.reference)⟩
    have hHeader : header ∈ directory.headers := List.mem_cons_of_mem outer
      (GeneralPaperFieldDirectoryLookup.collect_header_member dirs routeDir hRouteMem header (List.mem_singleton_self _))
    have hCellGlobal : cell ∈ directory.cells := GeneralPaperFieldDirectoryLookup.collect_cell_member dirs routeDir hRouteMem cell hCell
    have hLength := congrArg List.length hValues
    simp only [List.length_map] at hLength
    have hField : field.val < header.targets.length := by
      change field.val < (routeDir.cells.map (fun cell => cell.region.reference)).length
      rw [List.length_map,hLength]
      exact field.isLt
    rw [List.getElem?_eq_getElem hField] at hTarget
    have hTargetEq := Option.some.inj hTarget
    change header.targets[field.val] = cell.region.reference at hTargetEq
    have h := (GeneralPaperRecordScalarRead.field_at model S A start plan directory hSafe hCovered hPos hA hCap
      header hHeader rfl cell hCellGlobal ⟨field.val,hField⟩ hTargetEq).1
    rw [hValue] at h
    exact h
  exact ⟨routeDir.root.reference,trace model A installed i.val routeDir.root.reference _ hPointer hDecoded⟩

end Blotto.GeneralPaperRouteArrayRead
