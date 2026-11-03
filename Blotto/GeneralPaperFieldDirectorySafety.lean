import Blotto.GeneralPaperFieldDirectory

/-! Field directories inherit ownership from actual allocated region order.
Appending disjoint consecutive components preserves header/cell order, valid
header lengths and scalar fit. These are proofs about constructor output,
not schema/non-aliasing certificates supplied during execution. -/
namespace Blotto.GeneralPaperFieldDirectorySafety
open GeneralPaperFieldDirectory GeneralPaperSequentialLayout GeneralPaperReferenceRegionSlots
open GeneralPaperScalarFieldCursor (Cell)
open GeneralPaperRetainedScalarValue (Scalar encode)
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192

def Safe {A : ℕ} (regions : List (Region A)) (directory : Directory A) : Prop :=
  directory.root ∈ regions ∧ (directory.headers.map Header.region).Sublist regions ∧
    (directory.cells.map Cell.region).Sublist regions ∧ (∀ header ∈ directory.headers,Valid header) ∧
    ∀ cell ∈ directory.cells,cell.Fits

def SafeBody {A : ℕ} (regions : List (Region A)) (body : Body A) : Prop :=
  (∀ root ∈ body.roots,root ∈ regions) ∧ (body.headers.map Header.region).Sublist regions ∧
    (body.cells.map Cell.region).Sublist regions ∧ (∀ header ∈ body.headers,Valid header) ∧
    ∀ cell ∈ body.cells,cell.Fits

theorem mono {A : ℕ} (first full : List (Region A)) (directory : Directory A)
    (hSafe : Safe first directory) (hSub : first.Sublist full) : Safe full directory :=
  ⟨hSub.subset hSafe.1,hSafe.2.1.trans hSub,hSafe.2.2.1.trans hSub,hSafe.2.2.2⟩

theorem prepend (S A : ℕ) (first rest : List (Region A)) (directory : Directory A) (tail : Body A)
    (hFirst : Safe first directory) (hRest : SafeBody rest tail) :
    SafeBody (first ++ rest) (GeneralPaperFieldDirectory.prepend S A directory tail).1 := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · rw [prepend_roots]
    intro root hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact List.mem_append_left _ hFirst.1
    · exact List.mem_append_right _ (hRest.1 root hr)
  · rw [prepend_headers,List.map_append]
    exact hFirst.2.1.append hRest.2.1
  · rw [prepend_cells,List.map_append]
    exact hFirst.2.2.1.append hRest.2.2.1
  · rw [prepend_headers]
    intro header hh
    rcases List.mem_append.mp hh with hh | hh
    · exact hFirst.2.2.2.1 header hh
    · exact hRest.2.2.2.1 header hh
  · rw [prepend_cells]
    intro cell hc
    rcases List.mem_append.mp hc with hc | hc
    · exact hFirst.2.2.2.2 cell hc
    · exact hRest.2.2.2.2 cell hc

theorem scalar_array (model : RationalCostModel) (S A start : ℕ) (values : List Scalar) :
    Safe (GeneralPaperSequentialLayout.run model S A start (A * (64 + values.length) :: values.map encode)).1
      (ofArray (GeneralPaperMappedScalarArrayCursor.expected model S A start values)) := by
  let header := GeneralPaperScalarArrayFieldCursor.layoutHeader A start values.length
  let regions := (GeneralPaperSequentialLayout.run model S A (start + A * (64 + values.length)) (values.map encode)).1
  have hLength : regions.length = values.length := by dsimp only [regions]; rw [GeneralPaperSequentialLayout.count,List.length_map]
  rw [GeneralPaperScalarArrayFieldCursor.layout_regions]
  refine ⟨List.mem_cons_self ..,?_,?_,?_,?_⟩
  · change [header].Sublist (header :: regions)
    exact (List.nil_sublist regions).cons_cons header
  · change ((GeneralPaperScalarFieldCursor.cells A regions values).map Cell.region).Sublist (header :: regions)
    rw [GeneralPaperScalarFieldCursor.cells_regions A regions values hLength]
    exact (List.Sublist.refl regions).cons header
  · intro h hh
    have hHeader : h = (GeneralPaperMappedScalarArrayCursor.expected model S A start values).header := List.mem_singleton.mp hh
    subst h
    exact GeneralPaperScalarArrayFieldCursor.header_valid A header regions values hLength rfl
  · exact GeneralPaperScalarFieldCursor.cells_fit A regions values (GeneralPaperSequentialLayout.lengths model S A _ _)

theorem scalar_rational {n : ℕ} (model : RationalCostModel) (S A start : ℕ) (source : FixedArrayTable n ℚ) :
    Safe (GeneralPaperMeasuredBlockLayout.run model S A start
      (GeneralPaperMeasuredArrayBlockPlan.array model S A (GeneralPaperMeasuredBlockPlan.rational model S) source)).1
      (ofArray (GeneralPaperMappedScalarArrayCursor.expected model S A start (source.data.toList.map Scalar.rational))) := by
  change Safe (GeneralPaperSequentialLayout.run model S A start _).1 _
  rw [GeneralPaperMappedScalarArrayCursor.rational_plan]
  exact scalar_array model S A start _

theorem scalar_natural {n : ℕ} (model : RationalCostModel) (S A start : ℕ) (source : FixedArrayTable n ℕ) :
    Safe (GeneralPaperMeasuredBlockLayout.run model S A start
      (GeneralPaperMeasuredArrayBlockPlan.array model S A (GeneralPaperMeasuredBlockPlan.natural model S) source)).1
      (ofArray (GeneralPaperMappedScalarArrayCursor.expected model S A start (source.data.toList.map Scalar.natural))) := by
  change Safe (GeneralPaperSequentialLayout.run model S A start _).1 _
  rw [GeneralPaperMappedScalarArrayCursor.natural_plan]
  exact scalar_array model S A start _

end Blotto.GeneralPaperFieldDirectorySafety
