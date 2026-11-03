import Blotto.GeneralPaperStoredBooleanRowRead

/-! A retained row-list follows its actual indexed reference and exposes its
stored count. Schemas and selected source rows are erased proof observers. -/
namespace Blotto.GeneralPaperStoredListChildRead
open GeneralPaperFieldDirectory GeneralPaperSequentialLayout GeneralPaperReferenceRegionSlots
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperSamplerRecordInstallation (Readback)
open GeneralPaperHeaderCountInstallation (Contract)
open GeneralPaperUnifiedFieldValue
open GeneralPaperMixedReferenceMemory (Word)
open GeneralPaperStoredChildRead (Child load trace)
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 8192

theorem child {α : Type*} (model : RationalCostModel) (A start : ℕ) (installed : Installed A)
    (schema : α → List ℕ) (expected : α → ℕ → Directory A) (values : List α)
    (hRead : Readback model A installed (GeneralPaperFrontDirectoryList.expected A start schema expected values))
    (hRoot : installed.root = (GeneralPaperFrontDirectoryList.expected A start schema expected values).root.reference)
    (index : Fin values.length) :
    ∃ fieldStart,
      (load model A installed 32 index.val).1 =
        some (⟨A,GeneralPaperStoredScalarRead.atRoot installed (expected values[index.val] fieldStart).root.reference⟩ : Child) ∧
      (GeneralPaperMixedReferenceRegionProgram.read model A (referenceMemory installed.memory) installed.root 32 index.val).1 =
        some (⟨A,(expected values[index.val] fieldStart).root.reference⟩ : Word) ∧
      Readback model A (GeneralPaperStoredScalarRead.atRoot installed (expected values[index.val] fieldStart).root.reference)
        (expected values[index.val] fieldStart) ∧
      (∀ header ∈ (expected values[index.val] fieldStart).headers,
        header ∈ (GeneralPaperFrontDirectoryList.expected A start schema expected values).headers) ∧
      (∀ cell ∈ (expected values[index.val] fieldStart).cells,
        cell ∈ (GeneralPaperFrontDirectoryList.expected A start schema expected values).cells) := by
  let dirs := GeneralPaperChildDirectorySpecification.directories schema expected (start + A * (2 * values.length + 32)) values
  let body := GeneralPaperChildDirectorySpecification.collect dirs
  let directory := GeneralPaperFrontDirectoryList.expected A start schema expected values
  have hLength : dirs.length = values.length := GeneralPaperChildDirectorySpecification.directory_count _ _ _ _
  have hIndex : index.val < dirs.length := by rw [hLength]; exact index.isLt
  obtain ⟨fieldStart,hLookup⟩ := GeneralPaperFieldDirectoryLookup.child_lookup schema expected (start + A * (2 * values.length + 32)) values index.val index.isLt
  rw [List.getElem?_eq_getElem hIndex] at hLookup
  let child := expected values[index.val] fieldStart
  have hEq : dirs[index.val] = child := Option.some.inj hLookup
  have hMember : child ∈ dirs := by rw [← hEq]; exact List.getElem_mem hIndex
  let header : Header A := ⟨directory.root,32,body.roots.map Region.reference⟩
  have hHeader : header ∈ directory.headers := List.mem_cons_self ..
  have hTargetIndex : index.val < header.targets.length := by
    change index.val < (dirs.map Directory.root |>.map Region.reference).length
    rw [List.length_map,List.length_map,hLength]
    exact index.isLt
  have hTarget : header.targets[index.val]? = some child.root.reference := by
    change ((dirs.map Directory.root).map Region.reference)[index.val]? = _
    rw [List.getElem?_map,List.getElem?_map,List.getElem?_eq_getElem hIndex,hEq]
    rfl
  rw [List.getElem?_eq_getElem hTargetIndex] at hTarget
  have hPointer := hRead.1 header hHeader ⟨index.val,hTargetIndex⟩
  rw [Option.some.inj hTarget] at hPointer
  change (GeneralPaperMixedReferenceRegionProgram.read model A (referenceMemory installed.memory) directory.root.reference 32 index.val).1 =
    some (⟨A,child.root.reference⟩ : Word) at hPointer
  rw [← hRoot] at hPointer
  have hHeaders : ∀ h ∈ child.headers,h ∈ directory.headers := by
    intro h hh
    exact List.mem_cons_of_mem header (GeneralPaperFieldDirectoryLookup.collect_header_member dirs child hMember h hh)
  have hCells : ∀ c ∈ child.cells,c ∈ directory.cells := by
    intro c hc
    exact GeneralPaperFieldDirectoryLookup.collect_cell_member dirs child hMember c hc
  exact ⟨fieldStart,(trace model A installed 32 index.val child.root.reference hPointer).1,hPointer,
    GeneralPaperHeaderCountReadback.restrict model A installed directory child hRead hHeaders hCells,hHeaders,hCells⟩


theorem count_source {α : Type*} (model : RationalCostModel) (A start : ℕ) (installed : Installed A)
    (full : Directory A) (hContract : Contract model A installed full)
    (schema : α → List ℕ) (expected : α → ℕ → Directory A) (values : List α)
    (hHeaders : ∀ header ∈ (GeneralPaperFrontDirectoryList.expected A start schema expected values).headers,header ∈ full.headers)
    (hRoot : installed.root = (GeneralPaperFrontDirectoryList.expected A start schema expected values).root.reference) :
    (GeneralPaperHeaderCountReadback.count model A installed installed.root).1 = some values.length := by
  let dirs := GeneralPaperChildDirectorySpecification.directories schema expected (start + A * (2 * values.length + 32)) values
  let header : Header A := ⟨(GeneralPaperFrontDirectoryList.expected A start schema expected values).root,32,
    (GeneralPaperChildDirectorySpecification.collect dirs).roots.map Region.reference⟩
  have hh : header ∈ full.headers := hHeaders header (List.mem_cons_self ..)
  have h := GeneralPaperRetainedHeaderCountSources.children model A installed full hContract header hh (by change (32 : ℕ) ≠ 0; decide)
    schema expected (start + A * (2 * values.length + 32)) values rfl
  rw [hRoot]
  exact h

end Blotto.GeneralPaperStoredListChildRead
