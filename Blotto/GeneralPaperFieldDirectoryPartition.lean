import Blotto.GeneralPaperMatrixFieldInstallation

/-! Complete owner partitions complement the separately ordered Safe lists.
Together, header owners and scalar owners are a permutation of the actual
allocated regions. The proof is preserved by priced child aggregation and
holds for actual scalar-array and matrix constructor output. -/
namespace Blotto.GeneralPaperFieldDirectoryPartition
open GeneralPaperFieldDirectory GeneralPaperSequentialLayout GeneralPaperReferenceRegionSlots
open GeneralPaperScalarFieldCursor (Cell)
open GeneralPaperRetainedScalarValue (Scalar encode)
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192

def Covered {A : ℕ} (regions : List (Region A)) (directory : Directory A) : Prop :=
  (directory.headers.map Header.region ++ directory.cells.map Cell.region).Perm regions

def CoveredBody {A : ℕ} (regions : List (Region A)) (body : Body A) : Prop :=
  (body.headers.map Header.region ++ body.cells.map Cell.region).Perm regions

theorem shuffle {α : Type*} (first second third fourth : List α) :
    ((first ++ second) ++ (third ++ fourth)).Perm ((first ++ third) ++ (second ++ fourth)) := by
  have h : (second ++ third).Perm (third ++ second) := List.perm_append_comm
  simpa only [List.append_assoc] using (h.append_right fourth).append_left first

theorem prepend (S A : ℕ) (first rest : List (Region A)) (directory : Directory A) (tail : Body A)
    (hFirst : Covered first directory) (hRest : CoveredBody rest tail) :
    CoveredBody (first ++ rest) (GeneralPaperFieldDirectory.prepend S A directory tail).1 := by
  unfold CoveredBody
  rw [prepend_headers,prepend_cells,List.map_append,List.map_append]
  exact (shuffle _ _ _ _).trans (hFirst.append hRest)

theorem scalar_array (model : RationalCostModel) (S A start : ℕ) (values : List Scalar) :
    Covered (GeneralPaperSequentialLayout.run model S A start (A * (64 + values.length) :: values.map encode)).1
      (ofArray (GeneralPaperMappedScalarArrayCursor.expected model S A start values)) := by
  let header := GeneralPaperScalarArrayFieldCursor.layoutHeader A start values.length
  let regions := (GeneralPaperSequentialLayout.run model S A (start + A * (64 + values.length)) (values.map encode)).1
  have hLength : regions.length = values.length := by dsimp only [regions]; rw [GeneralPaperSequentialLayout.count,List.length_map]
  rw [GeneralPaperScalarArrayFieldCursor.layout_regions]
  change (header :: (GeneralPaperScalarFieldCursor.cells A regions values).map Cell.region).Perm (header :: regions)
  rw [GeneralPaperScalarFieldCursor.cells_regions A regions values hLength]

theorem scalar_rational {n : ℕ} (model : RationalCostModel) (S A start : ℕ) (source : FixedArrayTable n ℚ) :
    Covered (GeneralPaperMeasuredBlockLayout.run model S A start
      (GeneralPaperMeasuredArrayBlockPlan.array model S A (GeneralPaperMeasuredBlockPlan.rational model S) source)).1
      (ofArray (GeneralPaperMappedScalarArrayCursor.expected model S A start (source.data.toList.map Scalar.rational))) := by
  change Covered (GeneralPaperSequentialLayout.run model S A start _).1 _
  rw [GeneralPaperMappedScalarArrayCursor.rational_plan]
  exact scalar_array model S A start _

theorem scalar_natural {n : ℕ} (model : RationalCostModel) (S A start : ℕ) (source : FixedArrayTable n ℕ) :
    Covered (GeneralPaperMeasuredBlockLayout.run model S A start
      (GeneralPaperMeasuredArrayBlockPlan.array model S A (GeneralPaperMeasuredBlockPlan.natural model S) source)).1
      (ofArray (GeneralPaperMappedScalarArrayCursor.expected model S A start (source.data.toList.map Scalar.natural))) := by
  change Covered (GeneralPaperSequentialLayout.run model S A start _).1 _
  rw [GeneralPaperMappedScalarArrayCursor.natural_plan]
  exact scalar_array model S A start _

theorem children {α : Type*} (model : RationalCostModel) (S A : ℕ) (schema : α → List ℕ) (expected : α → ℕ → Directory A)
    (hEach : ∀ value start,Covered (GeneralPaperSequentialLayout.run model S A start (schema value)).1 (expected value start))
    (start : ℕ) (values : List α) :
    CoveredBody (GeneralPaperSequentialLayout.run model S A start (values.map schema).flatten).1
      (GeneralPaperChildDirectorySpecification.collect (GeneralPaperChildDirectorySpecification.directories schema expected start values)) := by
  induction values generalizing start with
  | nil => exact List.Perm.refl []
  | cons value values ih =>
    rw [GeneralPaperChildDirectorySpecification.directories,GeneralPaperChildDirectorySpecification.collect_cons S A,
      List.map_cons,List.flatten_cons,GeneralPaperMeasuredLayoutComposition.regions_append,GeneralPaperSequentialLayout.cursor]
    exact prepend S A _ _ _ _ (hEach value start) (ih (start + (schema value).sum))

theorem compose (A : ℕ) (header : Region A) (regions : List (Region A)) (body : Body A)
    (hBody : CoveredBody regions body) : Covered (header :: regions) (GeneralPaperNestedArrayFieldCursor.compose header body) :=
  hBody.cons header

theorem matrix {m r : ℕ} (model : RationalCostModel) (S A start : ℕ) (source : FixedArrayTable r (FixedArrayTable m ℚ)) :
    Covered (GeneralPaperMeasuredBlockLayout.run model S A start (GeneralPaperEqualMeasuredRetainedPlan.matrix model S A source)).1
      (GeneralPaperMatrixFieldCursor.expected model S A start source) := by
  have hEach : ∀ row : FixedArrayTable m ℚ,∀ start,Covered
      (GeneralPaperSequentialLayout.run model S A start (GeneralPaperMatrixFieldCursor.rowSchema model S A row)).1
      (GeneralPaperMatrixFieldCursor.rowExpected model S A row start) := by
    intro row start
    exact scalar_rational model S A start row
  have hBody := children model S A (GeneralPaperMatrixFieldCursor.rowSchema model S A)
    (GeneralPaperMatrixFieldCursor.rowExpected model S A) hEach
    (start + A * (64 + source.data.toList.length)) source.data.toList
  have h := compose A (GeneralPaperScalarArrayFieldCursor.layoutHeader A start source.data.toList.length) _ _ hBody
  change Covered (GeneralPaperSequentialLayout.run model S A start _).1 _
  rw [GeneralPaperMatrixFieldCursor.plan]
  simpa only [GeneralPaperSequentialLayout.run,GeneralPaperStoredWordEncoding.word_data,
    GeneralPaperScalarArrayFieldCursor.layoutHeader,GeneralPaperMatrixFieldCursor.expected] using h

end Blotto.GeneralPaperFieldDirectoryPartition
