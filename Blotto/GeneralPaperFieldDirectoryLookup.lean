import Blotto.GeneralPaperFieldDirectoryInstallation

/-! Erased indexed correspondence for extracted child directories and scalar
cells. Readers receive only raw roots/indices; these lemmas identify the
actual installed targets with source-indexed values after construction. -/
namespace Blotto.GeneralPaperFieldDirectoryLookup
open GeneralPaperFieldDirectory GeneralPaperSequentialLayout
open GeneralPaperRetainedScalarValue
open GeneralPaperScalarFieldCursor (Cell)
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192

theorem child_lookup {α : Type*} {A : ℕ} (schema : α → List ℕ) (expected : α → ℕ → Directory A)
    (start : ℕ) (values : List α) (index : ℕ) (hIndex : index < values.length) :
    ∃ fieldStart,(GeneralPaperChildDirectorySpecification.directories schema expected start values)[index]? =
      some (expected values[index] fieldStart) := by
  induction values generalizing start index with
  | nil => simp only [List.length_nil] at hIndex; omega
  | cons value values ih =>
    cases index with
    | zero => exact ⟨start,rfl⟩
    | succ index =>
      have hTail : index < values.length := by simp only [List.length_cons] at hIndex; omega
      obtain ⟨fieldStart,h⟩ := ih (start + (schema value).sum) index hTail
      exact ⟨fieldStart,h⟩

theorem collect_header_member {A : ℕ} (directories : List (Directory A)) (directory : Directory A)
    (hDirectory : directory ∈ directories) (header : GeneralPaperReferenceRegionSlots.Header A) (hHeader : header ∈ directory.headers) :
    header ∈ (GeneralPaperChildDirectorySpecification.collect directories).headers :=
  List.mem_flatten.mpr ⟨directory.headers,List.mem_map.mpr ⟨directory,hDirectory,rfl⟩,hHeader⟩

theorem collect_cell_member {A : ℕ} (directories : List (Directory A)) (directory : Directory A)
    (hDirectory : directory ∈ directories) (cell : Cell A) (hCell : cell ∈ directory.cells) :
    cell ∈ (GeneralPaperChildDirectorySpecification.collect directories).cells :=
  List.mem_flatten.mpr ⟨directory.cells,List.mem_map.mpr ⟨directory,hDirectory,rfl⟩,hCell⟩

theorem array_target_count (model : RationalCostModel) (S A start : ℕ) (values : List Scalar) :
    (GeneralPaperMappedScalarArrayCursor.expected model S A start values).header.targets.length = values.length := by
  let regions := (GeneralPaperSequentialLayout.run model S A (start + A * (64 + values.length)) (values.map encode)).1
  have hLength : regions.length = values.length := by dsimp only [regions]; rw [GeneralPaperSequentialLayout.count,List.length_map]
  have h := congrArg List.length (GeneralPaperScalarFieldCursor.cells_values A regions values hLength)
  simp only [List.length_map] at h
  change ((GeneralPaperScalarFieldCursor.cells A regions values).map (fun cell => cell.region.reference)).length = values.length
  rw [List.length_map]
  exact h

theorem array_cell (model : RationalCostModel) (S A start : ℕ) (values : List Scalar) (index : ℕ) (hIndex : index < values.length) :
    ∃ cell,cell ∈ (GeneralPaperMappedScalarArrayCursor.expected model S A start values).cells ∧
      (GeneralPaperMappedScalarArrayCursor.expected model S A start values).header.targets[index]? = some cell.region.reference ∧
      cell.value = values[index] := by
  let regions := (GeneralPaperSequentialLayout.run model S A (start + A * (64 + values.length)) (values.map encode)).1
  let cells := GeneralPaperScalarFieldCursor.cells A regions values
  have hLength : regions.length = values.length := by dsimp only [regions]; rw [GeneralPaperSequentialLayout.count,List.length_map]
  have hValues := GeneralPaperScalarFieldCursor.cells_values A regions values hLength
  have hCount := congrArg List.length hValues
  simp only [List.length_map] at hCount
  have hCellIndex : index < cells.length := by dsimp only [cells]; rw [hCount]; exact hIndex
  let cell := cells[index]
  refine ⟨cell,List.getElem_mem hCellIndex,?_,?_⟩
  · change (cells.map (fun cell => cell.region.reference))[index]? = some cell.region.reference
    rw [List.getElem?_map,List.getElem?_eq_getElem hCellIndex]
    rfl
  · have h := congrArg (fun xs : List Scalar => xs[index]?) hValues
    rw [List.getElem?_map,List.getElem?_eq_getElem hCellIndex,List.getElem?_eq_getElem hIndex] at h
    exact Option.some.inj h

end Blotto.GeneralPaperFieldDirectoryLookup
