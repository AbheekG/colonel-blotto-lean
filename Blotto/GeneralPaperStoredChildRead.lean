import Blotto.GeneralPaperStoredMatrixRowRead

/-! A child loader follows an actual stored reference and keeps the same
memory. Directory and source-shape arguments occur only in correspondence. -/
namespace Blotto.GeneralPaperStoredChildRead
open GeneralPaperFieldDirectory GeneralPaperSequentialLayout GeneralPaperReferenceRegionSlots
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperSamplerRecordInstallation (Readback)
open GeneralPaperUnifiedFieldValue
open GeneralPaperMixedReferenceMemory (Word)
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 8192

abbrev Child := Σ A : ℕ,Installed A

def load (model : RationalCostModel) (A : ℕ) (installed : Installed A) (fixed index : ℕ) : Option Child × ℕ :=
  let pointer := GeneralPaperMixedReferenceRegionProgram.read model A (referenceMemory installed.memory) installed.root fixed index
  match pointer.1 with
  | none => (none,pointer.2 + 64 * (A + 1))
  | some ⟨B,root⟩ =>
    (some ⟨B,GeneralPaperStoredScalarRead.atRoot installed root⟩,pointer.2 + 64 * (A + B + 1))

theorem trace (model : RationalCostModel) (A : ℕ) (installed : Installed A) (fixed index : ℕ) (root : FixedBinaryWord A)
    (hPointer : (GeneralPaperMixedReferenceRegionProgram.read model A (referenceMemory installed.memory) installed.root fixed index).1 =
      some (⟨A,root⟩ : Word)) :
    (load model A installed fixed index).1 = some (⟨A,GeneralPaperStoredScalarRead.atRoot installed root⟩ : Child) ∧
      (load model A installed fixed index).2 =
        (GeneralPaperMixedReferenceRegionProgram.read model A (referenceMemory installed.memory) installed.root fixed index).2 + 128 * A + 64 := by
  simp only [load,hPointer]
  constructor
  · exact True.intro
  · ring

theorem record_child {α : Type*} (model : RationalCostModel) (A start arity : ℕ) (installed : Installed A)
    (schema : α → List ℕ) (expected : α → ℕ → Directory A) (values : List α)
    (hRead : Readback model A installed (GeneralPaperTrailingDirectoryRecord.expected A start arity schema expected values))
    (hRoot : installed.root = (GeneralPaperTrailingDirectoryRecord.expected A start arity schema expected values).root.reference)
    (index : Fin values.length) :
    ∃ fieldStart,
      (load model A installed 0 index.val).1 =
        some (⟨A,GeneralPaperStoredScalarRead.atRoot installed (expected values[index.val] fieldStart).root.reference⟩ : Child) ∧
      (GeneralPaperMixedReferenceRegionProgram.read model A (referenceMemory installed.memory) installed.root 0 index.val).1 =
        some (⟨A,(expected values[index.val] fieldStart).root.reference⟩ : Word) ∧
      Readback model A (GeneralPaperStoredScalarRead.atRoot installed (expected values[index.val] fieldStart).root.reference)
        (expected values[index.val] fieldStart) ∧
      (∀ header ∈ (expected values[index.val] fieldStart).headers,
        header ∈ (GeneralPaperTrailingDirectoryRecord.expected A start arity schema expected values).headers) ∧
      (∀ cell ∈ (expected values[index.val] fieldStart).cells,
        cell ∈ (GeneralPaperTrailingDirectoryRecord.expected A start arity schema expected values).cells) := by
  let dirs := GeneralPaperChildDirectorySpecification.directories schema expected start values
  let body := GeneralPaperChildDirectorySpecification.collect dirs
  let directory := GeneralPaperTrailingDirectoryRecord.expected A start arity schema expected values
  have hLength : dirs.length = values.length := GeneralPaperChildDirectorySpecification.directory_count _ _ _ _
  have hIndex : index.val < dirs.length := by rw [hLength]; exact index.isLt
  obtain ⟨fieldStart,hLookup⟩ := GeneralPaperFieldDirectoryLookup.child_lookup schema expected start values index.val index.isLt
  rw [List.getElem?_eq_getElem hIndex] at hLookup
  let child := expected values[index.val] fieldStart
  have hEq : dirs[index.val] = child := Option.some.inj hLookup
  have hMember : child ∈ dirs := by rw [← hEq]; exact List.getElem_mem hIndex
  let header : Header A := ⟨directory.root,0,body.roots.map Region.reference⟩
  have hHeader : header ∈ directory.headers := List.mem_append_right _ (List.mem_singleton_self _)
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
  change (GeneralPaperMixedReferenceRegionProgram.read model A (referenceMemory installed.memory) directory.root.reference 0 index.val).1 =
    some (⟨A,child.root.reference⟩ : Word) at hPointer
  rw [← hRoot] at hPointer
  have hHeaders : ∀ h ∈ child.headers,h ∈ directory.headers := by
    intro h hh
    exact List.mem_append_left _ (GeneralPaperFieldDirectoryLookup.collect_header_member dirs child hMember h hh)
  have hCells : ∀ c ∈ child.cells,c ∈ directory.cells := by
    intro c hc
    exact GeneralPaperFieldDirectoryLookup.collect_cell_member dirs child hMember c hc
  exact ⟨fieldStart,(trace model A installed 0 index.val child.root.reference hPointer).1,hPointer,
    GeneralPaperHeaderCountReadback.restrict model A installed directory child hRead hHeaders hCells,hHeaders,hCells⟩

end Blotto.GeneralPaperStoredChildRead
