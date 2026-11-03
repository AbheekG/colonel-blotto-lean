import Blotto.GeneralPaperStoredBooleanWordWork

/-! Actual record-child loads have one bounded reference read and fixed
control work. Measured ownership proves the record's target count fits;
all child shapes and indices below are erased correctness arguments. -/
namespace Blotto.GeneralPaperStoredRecordReadWork
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperFieldDirectory (Directory)
open GeneralPaperReferenceRegionSlots (Header)
open GeneralPaperStoredReadContext (Context)
open GeneralPaperSamplerRecordInstallation (Readback)
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 8192

def header {α : Type*} (A start arity : ℕ) (schema : α → List ℕ) (child : α → ℕ → Directory A) (values : List α) : Header A :=
  let directory := GeneralPaperTrailingDirectoryRecord.expected A start arity schema child values
  let body := GeneralPaperChildDirectorySpecification.collect (GeneralPaperChildDirectorySpecification.directories schema child start values)
  ⟨directory.root,0,body.roots.map GeneralPaperSequentialLayout.Region.reference⟩

theorem member {α : Type*} (A start arity : ℕ) (schema : α → List ℕ) (child : α → ℕ → Directory A) (values : List α) :
    header A start arity schema child values ∈ (GeneralPaperTrailingDirectoryRecord.expected A start arity schema child values).headers :=
  List.mem_append_right _ (List.mem_singleton_self _)

theorem count {α : Type*} (A start arity : ℕ) (schema : α → List ℕ) (child : α → ℕ → Directory A) (values : List α) :
    (header A start arity schema child values).targets.length = values.length := by
  change (((GeneralPaperChildDirectorySpecification.directories schema child start values).map Directory.root).map
    GeneralPaperSequentialLayout.Region.reference).length = _
  rw [List.length_map,List.length_map,GeneralPaperChildDirectorySpecification.directory_count]

theorem work {α : Type*} (model : RationalCostModel) (S A layoutStart start arity : ℕ) (plan : GeneralPaperMeasuredBlockPlan.Plan)
    (full : Directory A) (installed : Installed A) (ctx : Context model S A layoutStart plan full installed)
    (schema : α → List ℕ) (child : α → ℕ → Directory A) (values : List α)
    (hRead : Readback model A installed (GeneralPaperTrailingDirectoryRecord.expected A start arity schema child values))
    (hHeaders : ∀ h ∈ (GeneralPaperTrailingDirectoryRecord.expected A start arity schema child values).headers,h ∈ full.headers)
    (hRoot : installed.root = (GeneralPaperTrailingDirectoryRecord.expected A start arity schema child values).root.reference)
    (index : Fin values.length) :
    (GeneralPaperStoredChildRead.load model A installed 0 index.val).2 ≤
      GeneralPaperStoredReferenceReadWork.readBound model A A + 128 * A + 64 := by
  obtain ⟨fieldStart,_,hPointer,_,_,_⟩ := GeneralPaperStoredChildRead.record_child model A start arity installed schema child values hRead hRoot index
  have hCount := GeneralPaperStoredReadContext.header_count_fits ctx _ (hHeaders _ (member A start arity schema child values))
  rw [count] at hCount
  have hPointerWork := GeneralPaperStoredReferenceReadWork.read_work model A A 0 index.val _ installed.root
    (child values[index.val] fieldStart).root.reference (by decide) (index.isLt.trans hCount) hPointer
  rw [(GeneralPaperStoredChildRead.trace model A installed 0 index.val _ hPointer).2]
  exact Nat.add_le_add_right (Nat.add_le_add_right hPointerWork (128 * A)) 64

end Blotto.GeneralPaperStoredRecordReadWork
