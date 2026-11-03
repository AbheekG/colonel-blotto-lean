import Blotto.GeneralPaperPreparedRecordCursor

/-! A trailing record's installed slots recover its actual child roots.
Child selection also identifies the original-budget leaf in the prepared
cache; the actual pointer/payload reader recovers it from the same memory. -/
namespace Blotto.GeneralPaperDirectoryRecordRead
open GeneralPaperFieldDirectory GeneralPaperSequentialLayout GeneralPaperReferenceRegionSlots
open GeneralPaperFieldDirectorySafety GeneralPaperFieldDirectoryPartition
open GeneralPaperUnifiedFieldValue
open GeneralPaperMixedReferenceMemory (Word)
open GeneralPaperRetainedScalarValue (Scalar)
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 8192

theorem child_root (model : RationalCostModel) (S A start : ℕ) (plan : GeneralPaperMeasuredBlockPlan.Plan)
    (record : Region A) (body : Body A)
    (hSafe : Safe (GeneralPaperMeasuredBlockLayout.run model S A start plan).1 (GeneralPaperTrailingDirectoryRecord.compose record body))
    (hCovered : Covered (GeneralPaperMeasuredBlockLayout.run model S A start plan).1 (GeneralPaperTrailingDirectoryRecord.compose record body))
    (hA : 0 < A) (hCap : start + plan.sizes.sum < 2 ^ A) (index : Fin body.roots.length) :
    let installed := GeneralPaperUnifiedDirectoryInstallation.install model S A (GeneralPaperTrailingDirectoryRecord.compose record body)
    (GeneralPaperMixedReferenceRegionProgram.read model A (referenceMemory installed.memory) installed.root 0 index.val).1 =
      some (⟨A,(body.roots[index.val]).reference⟩ : Word) := by
  dsimp only
  have hRoot : (GeneralPaperUnifiedDirectoryInstallation.install model S A (GeneralPaperTrailingDirectoryRecord.compose record body)).root = record.reference := rfl
  rw [hRoot]
  let header : Header A := ⟨record,0,body.roots.map Region.reference⟩
  have hHeader : header ∈ (GeneralPaperTrailingDirectoryRecord.compose record body).headers :=
    List.mem_append_right _ (List.mem_singleton_self _)
  have hIndex : index.val < header.targets.length := by change index.val < (body.roots.map Region.reference).length; rw [List.length_map]; exact index.isLt
  have h := GeneralPaperUnifiedDirectoryInstallation.header_read model S A start plan
    (GeneralPaperTrailingDirectoryRecord.compose record body) hSafe hCovered hA hCap header hHeader ⟨index.val,hIndex⟩
  change (GeneralPaperMixedReferenceRegionProgram.read model A
    (referenceMemory (GeneralPaperUnifiedDirectoryInstallation.install model S A (GeneralPaperTrailingDirectoryRecord.compose record body)).memory)
    record.reference 0 index.val).1 = some (⟨A,header.targets[index.val]⟩ : Word) at h
  simpa only [header,List.getElem_map] using h

theorem prepared_child (model : RationalCostModel) (S A start : ℕ)
    {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
    (source : GeneralPaperEqualPreparedCache.Prepared G l) (hA : 0 < A)
    (hCap : start + (GeneralPaperEqualMeasuredRetainedPlan.prepared model S A source).sizes.sum < 2 ^ A)
    (index : Fin GeneralPaperPreparedRecordCursor.fields.length) :
    let dirs := GeneralPaperChildDirectorySpecification.directories (GeneralPaperPreparedRecordCursor.schema model S A source)
      (GeneralPaperPreparedRecordCursor.child model S A source) start GeneralPaperPreparedRecordCursor.fields
    ∃ fieldStart,
      (GeneralPaperMixedReferenceRegionProgram.read model A
        (referenceMemory (GeneralPaperUnifiedDirectoryInstallation.install model S A (GeneralPaperPreparedRecordCursor.expected model S A source start)).memory)
        (GeneralPaperUnifiedDirectoryInstallation.install model S A (GeneralPaperPreparedRecordCursor.expected model S A source start)).root 0 index.val).1 =
          some (⟨A,(GeneralPaperPreparedRecordCursor.child model S A source (GeneralPaperPreparedRecordCursor.fields[index.val]) fieldStart).root.reference⟩ : Word) ∧
      dirs[index.val]? = some (GeneralPaperPreparedRecordCursor.child model S A source (GeneralPaperPreparedRecordCursor.fields[index.val]) fieldStart) := by
  dsimp only
  let dirs := GeneralPaperChildDirectorySpecification.directories (GeneralPaperPreparedRecordCursor.schema model S A source)
    (GeneralPaperPreparedRecordCursor.child model S A source) start GeneralPaperPreparedRecordCursor.fields
  have hCount : dirs.length = GeneralPaperPreparedRecordCursor.fields.length := GeneralPaperChildDirectorySpecification.directory_count _ _ _ _
  have hIndex : index.val < dirs.length := by rw [hCount]; exact index.isLt
  obtain ⟨fieldStart,hLookup⟩ := GeneralPaperFieldDirectoryLookup.child_lookup (GeneralPaperPreparedRecordCursor.schema model S A source)
    (GeneralPaperPreparedRecordCursor.child model S A source) start GeneralPaperPreparedRecordCursor.fields index.val index.isLt
  refine ⟨fieldStart,?_,hLookup⟩
  obtain ⟨_,_,hs,hc⟩ := GeneralPaperPreparedRecordCursor.success model S A start source []
  have h := child_root model S A start (GeneralPaperEqualMeasuredRetainedPlan.prepared model S A source) _
    (GeneralPaperChildDirectorySpecification.collect dirs) hs hc hA hCap ⟨index.val,by
      change index.val < (dirs.map Directory.root).length
      rw [List.length_map]
      exact hIndex⟩
  rw [List.getElem?_eq_getElem hIndex] at hLookup
  have hMap := List.getElem_map Directory.root (l := dirs) (i := index.val) (h := by rw [List.length_map]; exact hIndex)
  have hRootMap := congrArg (fun region : Region A => some (⟨A,region.reference⟩ : Word)) hMap
  have hSelected := congrArg (fun directory : Directory A => some (⟨A,directory.root.reference⟩ : Word)) (Option.some.inj hLookup)
  exact h.trans (hRootMap.trans hSelected)

theorem prepared_budget (model : RationalCostModel) (S A start : ℕ)
    {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
    (source : GeneralPaperEqualPreparedCache.Prepared G l) (hA : 0 < A)
    (hCap : start + (GeneralPaperEqualMeasuredRetainedPlan.prepared model S A source).sizes.sum < 2 ^ A) :
    let installed := GeneralPaperUnifiedDirectoryInstallation.install model S A (GeneralPaperPreparedRecordCursor.expected model S A source start)
    (GeneralPaperRecordScalarRead.read model A installed 4).1 = some (.rational source.budget) ∧
      (GeneralPaperRecordScalarRead.read model A installed 4).2 =
        (GeneralPaperMixedReferenceRegionProgram.read model A (referenceMemory installed.memory) installed.root 0 4).2 +
        rationalWordWidth source.budget + 192 * A + 128 := by
  dsimp only
  let directory := GeneralPaperPreparedRecordCursor.expected model S A source start
  let dirs := GeneralPaperChildDirectorySpecification.directories (GeneralPaperPreparedRecordCursor.schema model S A source)
    (GeneralPaperPreparedRecordCursor.child model S A source) start GeneralPaperPreparedRecordCursor.fields
  obtain ⟨budgetStart,hPointer,hLookup⟩ := prepared_child model S A start source hA hCap ⟨4,by decide⟩
  let budgetDir := GeneralPaperPreparedRecordCursor.child model S A source .budget budgetStart
  let cell : GeneralPaperScalarFieldCursor.Cell A := ⟨budgetDir.root,.rational source.budget⟩
  have hCount : dirs.length = 5 := GeneralPaperChildDirectorySpecification.directory_count _ _ _ _
  have hIndex : 4 < dirs.length := by rw [hCount]; decide
  change dirs[4]? = some budgetDir at hLookup
  rw [List.getElem?_eq_getElem hIndex] at hLookup
  have hBudgetMem : budgetDir ∈ dirs := by rw [← Option.some.inj hLookup]; exact List.getElem_mem hIndex
  have hCell : cell ∈ directory.cells := GeneralPaperFieldDirectoryLookup.collect_cell_member dirs budgetDir hBudgetMem cell (List.mem_singleton_self _)
  obtain ⟨_,_,hSafe,_⟩ := GeneralPaperPreparedRecordCursor.success model S A start source []
  have hScalar := GeneralPaperUnifiedDirectoryInstallation.scalar_read model S A start
    (GeneralPaperEqualMeasuredRetainedPlan.prepared model S A source) directory hSafe
    (GeneralPaperEqualMeasuredPlanPositive.prepared model S A source hA) hCap cell hCell
  exact GeneralPaperRecordScalarRead.trace model A _ 4 budgetDir.root.reference (.rational source.budget) hPointer hScalar

end Blotto.GeneralPaperDirectoryRecordRead
