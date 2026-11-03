import Blotto.GeneralPaperStoredRouteReadback

/-! Indexed route reads and the actual stored route count are recovered
inside a larger sampler directory, without rebuilding or reinstalling it. -/
namespace Blotto.GeneralPaperStoredRouteArraySource
open GeneralPaperFieldDirectory GeneralPaperSequentialLayout GeneralPaperReferenceRegionSlots
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperSamplerRecordInstallation (Readback)
open GeneralPaperHeaderCountInstallation (Contract)
open GeneralPaperUnifiedFieldValue
open GeneralPaperMixedReferenceMemory (Word)
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 8192

theorem source {n m : ℕ} (model : RationalCostModel) (S A start : ℕ) (installed : Installed A)
    (routes : FixedArrayTable n (GroupRoute m))
    (hRead : Readback model A installed (GeneralPaperRouteArrayCursor.expected model S A start routes))
    (hRoot : installed.root = (GeneralPaperRouteArrayCursor.expected model S A start routes).root.reference) (index : Fin n) :
    ∃ root : FixedBinaryWord A,
      (GeneralPaperRouteArrayRead.read model A installed index.val).1 = some ((routes.read index).1.map Fin.val,(routes.read index).2) ∧
      (GeneralPaperRouteArrayRead.read model A installed index.val).2 =
        (GeneralPaperMixedReferenceRegionProgram.read model A (referenceMemory installed.memory) installed.root 64 index.val).2 +
        (GeneralPaperRouteFieldRead.read model A (GeneralPaperStoredScalarRead.atRoot installed root)).2 + 128 * A + 64 := by
  let directory := GeneralPaperRouteArrayCursor.expected model S A start routes
  let values := routes.data.toList
  let dirs := GeneralPaperChildDirectorySpecification.directories (GeneralPaperRouteArrayCursor.schema model S A)
    (GeneralPaperRouteFieldCursor.expected model S A) (start + A * (64 + values.length)) values
  have hIndex : index.val < values.length := by dsimp only [values]; rw [Array.length_toList,routes.size]; exact index.isLt
  have hLength : dirs.length = values.length := GeneralPaperChildDirectorySpecification.directory_count _ _ _ _
  have hDirIndex : index.val < dirs.length := by rw [hLength]; exact hIndex
  obtain ⟨fieldStart,hLookup⟩ := GeneralPaperFieldDirectoryLookup.child_lookup (GeneralPaperRouteArrayCursor.schema model S A)
    (GeneralPaperRouteFieldCursor.expected model S A) (start + A * (64 + values.length)) values index.val hIndex
  have hValue : values[index.val] = routes.read index := by simp only [values,Array.getElem_toList,FixedArrayTable.read]
  rw [hValue,List.getElem?_eq_getElem hDirIndex] at hLookup
  let child := GeneralPaperRouteFieldCursor.expected model S A (routes.read index) fieldStart
  have hEq : dirs[index.val] = child := Option.some.inj hLookup
  have hChild : child ∈ dirs := by rw [← hEq]; exact List.getElem_mem hDirIndex
  let header : Header A := ⟨directory.root,64,(dirs.map Directory.root).map Region.reference⟩
  have hHeader : header ∈ directory.headers := List.mem_cons_self ..
  have hTargetIndex : index.val < header.targets.length := by
    change index.val < ((dirs.map Directory.root).map Region.reference).length
    rw [List.length_map,List.length_map,hLength]
    exact hIndex
  have hTarget : header.targets[index.val]? = some child.root.reference := by
    change ((dirs.map Directory.root).map Region.reference)[index.val]? = _
    rw [List.getElem?_map,List.getElem?_map,List.getElem?_eq_getElem hDirIndex,hEq]
    rfl
  rw [List.getElem?_eq_getElem hTargetIndex] at hTarget
  have hPointer := hRead.1 header hHeader ⟨index.val,hTargetIndex⟩
  rw [Option.some.inj hTarget] at hPointer
  change (GeneralPaperMixedReferenceRegionProgram.read model A (referenceMemory installed.memory) directory.root.reference 64 index.val).1 =
    some (⟨A,child.root.reference⟩ : Word) at hPointer
  rw [← hRoot] at hPointer
  have hHeaders : ∀ h ∈ child.headers,h ∈ directory.headers := by
    intro h hh
    exact List.mem_cons_of_mem header (GeneralPaperFieldDirectoryLookup.collect_header_member dirs child hChild h hh)
  have hCells : ∀ c ∈ child.cells,c ∈ directory.cells := by
    intro c hc
    exact GeneralPaperFieldDirectoryLookup.collect_cell_member dirs child hChild c hc
  have hChildRead := GeneralPaperHeaderCountReadback.restrict model A installed directory child hRead hHeaders hCells
  have hRoute := GeneralPaperStoredRouteReadback.source model S A fieldStart
    (GeneralPaperStoredScalarRead.atRoot installed child.root.reference) (routes.read index) hChildRead rfl
  exact ⟨child.root.reference,GeneralPaperRouteArrayRead.trace model A installed index.val child.root.reference _ hPointer hRoute⟩

theorem count_source {n m : ℕ} (model : RationalCostModel) (S A start : ℕ) (installed : Installed A) (full : Directory A)
    (hContract : Contract model A installed full) (routes : FixedArrayTable n (GroupRoute m))
    (hHeaders : ∀ header ∈ (GeneralPaperRouteArrayCursor.expected model S A start routes).headers,header ∈ full.headers)
    (hRoot : installed.root = (GeneralPaperRouteArrayCursor.expected model S A start routes).root.reference) :
    (GeneralPaperHeaderCountReadback.count model A installed installed.root).1 = some n := by
  let values := routes.data.toList
  let schema : GroupRoute m → List ℕ := GeneralPaperRouteArrayCursor.schema model S A
  let expected : GroupRoute m → ℕ → Directory A := GeneralPaperRouteFieldCursor.expected model S A
  let dirs := GeneralPaperChildDirectorySpecification.directories schema expected (start + A * (64 + values.length)) values
  let header : Header A := ⟨(GeneralPaperRouteArrayCursor.expected model S A start routes).root,64,
    (GeneralPaperChildDirectorySpecification.collect dirs).roots.map Region.reference⟩
  have hh : header ∈ full.headers := hHeaders header (List.mem_cons_self ..)
  have h := GeneralPaperRetainedHeaderCountSources.children model A installed full hContract header hh (by change (64 : ℕ) ≠ 0; decide)
    schema expected (start + A * (64 + values.length)) values rfl
  rw [hRoot]
  simpa only [values,Array.length_toList,routes.size] using h

end Blotto.GeneralPaperStoredRouteArraySource
