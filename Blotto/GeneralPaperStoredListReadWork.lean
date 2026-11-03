import Blotto.GeneralPaperStoredBooleanRowWork

/-! Front-header list access derives counts and valid indices from its
actual measured header. Only the selected child is loaded; the price is
one reference read and fixed root/control work. -/
namespace Blotto.GeneralPaperStoredListReadWork
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperFieldDirectory (Directory)
open GeneralPaperReferenceRegionSlots (Header)
open GeneralPaperStoredReadContext (Context)
open GeneralPaperSamplerRecordInstallation (Readback)
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 8192

def header {α : Type*} (A start : ℕ) (schema : α → List ℕ) (child : α → ℕ → Directory A) (values : List α) : Header A :=
  let directory := GeneralPaperFrontDirectoryList.expected A start schema child values
  let body := GeneralPaperChildDirectorySpecification.collect
    (GeneralPaperChildDirectorySpecification.directories schema child (start + A * (2 * values.length + 32)) values)
  ⟨directory.root,32,body.roots.map GeneralPaperSequentialLayout.Region.reference⟩

theorem count {α : Type*} (A start : ℕ) (schema : α → List ℕ) (child : α → ℕ → Directory A) (values : List α) :
    (header A start schema child values).targets.length = values.length := by
  change (((GeneralPaperChildDirectorySpecification.directories schema child (start + A * (2 * values.length + 32)) values).map Directory.root).map
    GeneralPaperSequentialLayout.Region.reference).length = _
  rw [List.length_map,List.length_map,GeneralPaperChildDirectorySpecification.directory_count]

theorem capacity {α : Type*} {model : RationalCostModel} {S A layoutStart : ℕ} {plan : GeneralPaperMeasuredBlockPlan.Plan}
    {full : Directory A} {installed : Installed A} (ctx : Context model S A layoutStart plan full installed)
    (start : ℕ) (schema : α → List ℕ) (child : α → ℕ → Directory A) (values : List α)
    (hHeaders : ∀ h ∈ (GeneralPaperFrontDirectoryList.expected A start schema child values).headers,h ∈ full.headers) : values.length < 2 ^ A := by
  have h := GeneralPaperStoredReadContext.header_count_fits ctx (header A start schema child values) (hHeaders _ (List.mem_cons_self ..))
  rwa [count] at h

theorem count_work {α : Type*} (model : RationalCostModel) (S A layoutStart start : ℕ) (plan : GeneralPaperMeasuredBlockPlan.Plan)
    (full : Directory A) (installed : Installed A) (ctx : Context model S A layoutStart plan full installed)
    (schema : α → List ℕ) (child : α → ℕ → Directory A) (values : List α)
    (hHeaders : ∀ h ∈ (GeneralPaperFrontDirectoryList.expected A start schema child values).headers,h ∈ full.headers)
    (hRoot : installed.root = (GeneralPaperFrontDirectoryList.expected A start schema child values).root.reference) :
    (GeneralPaperHeaderCountReadback.count model A installed installed.root).2 ≤ GeneralPaperStoredCountReadWork.bound model A := by
  have h := GeneralPaperStoredCountReadWork.work model A installed full ctx.contract (header A start schema child values)
    (hHeaders _ (List.mem_cons_self ..)) (by change (32 : ℕ) ≠ 0; decide)
  change (GeneralPaperHeaderCountReadback.count model A installed
    (GeneralPaperFrontDirectoryList.expected A start schema child values).root.reference).2 ≤ _ at h
  rwa [← hRoot] at h

theorem work {α : Type*} (model : RationalCostModel) (S A layoutStart start : ℕ) (plan : GeneralPaperMeasuredBlockPlan.Plan)
    (full : Directory A) (installed : Installed A) (ctx : Context model S A layoutStart plan full installed)
    (schema : α → List ℕ) (child : α → ℕ → Directory A) (values : List α)
    (hRead : Readback model A installed (GeneralPaperFrontDirectoryList.expected A start schema child values))
    (hHeaders : ∀ h ∈ (GeneralPaperFrontDirectoryList.expected A start schema child values).headers,h ∈ full.headers)
    (hRoot : installed.root = (GeneralPaperFrontDirectoryList.expected A start schema child values).root.reference) (index : Fin values.length) :
    (GeneralPaperStoredChildRead.load model A installed 32 index.val).2 ≤
      GeneralPaperStoredReferenceReadWork.readBound model A A + 128 * A + 64 := by
  obtain ⟨fieldStart,_,hPointer,_,_,_⟩ := GeneralPaperStoredListChildRead.child model A start installed schema child values hRead hRoot index
  have hPointerWork := GeneralPaperStoredReferenceReadWork.read_work model A A 32 index.val _ installed.root
    (child values[index.val] fieldStart).root.reference (by decide) (index.isLt.trans (capacity ctx start schema child values hHeaders)) hPointer
  rw [(GeneralPaperStoredChildRead.trace model A installed 32 index.val _ hPointer).2]
  exact Nat.add_le_add_right (Nat.add_le_add_right hPointerWork (128 * A)) 64

end Blotto.GeneralPaperStoredListReadWork
