import Blotto.GeneralPaperStoredDominantInstallation

/-! A dominant draw follows its actual row child, loads the initialized row
count, copies each rational coordinate and materializes the full array once.
Neither the source row nor its dimension is an execution input. -/
namespace Blotto.GeneralPaperStoredDominantEmission
open GeneralPaperFieldDirectory
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperHeaderCountInstallation (Contract)
open GeneralPaperStoredChildRead (Child)
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 8192

def run (model : RationalCostModel) (A : ℕ) (installed : Installed A) : GeneralPaperStoredRouteEmission.Result :=
  let child := GeneralPaperStoredChildRead.load model A installed 0 0
  match child.1 with
  | none => ⟨none,0,child.2 + 64 * (A + 1)⟩
  | some ⟨B,loaded⟩ =>
    let actual := GeneralPaperStoredReadStream.rationals model B loaded
    match actual.values with
    | none => ⟨none,actual.count,child.2 + actual.work + 64 * (A + B + 1)⟩
    | some values =>
      let buffer := PaperListReferenceArray.run (fun w => w) B values
      ⟨some buffer.1,actual.count,child.2 + actual.work + buffer.2 + 128 * (A + B + 1)⟩

theorem source {n : ℕ} (model : RationalCostModel) (S A start chosen : ℕ) (installed : Installed A)
    (row : RationalResourceArray n)
    (hContract : Contract model A installed (GeneralPaperStoredDominantCursor.expected model S A chosen row start))
    (hRoot : installed.root = (GeneralPaperStoredDominantCursor.expected model S A chosen row start).root.reference) :
    ∃ root : FixedBinaryWord A,
      (run model A installed).values = some row.data ∧ (run model A installed).count = n ∧
      (run model A installed).work = (GeneralPaperStoredChildRead.load model A installed 0 0).2 +
        (GeneralPaperStoredReadStream.rationals model A (GeneralPaperStoredScalarRead.atRoot installed root)).work +
        (PaperListReferenceArray.run (fun w => w) A row.data.toList).2 + 128 * (A + A + 1) := by
  obtain ⟨fieldStart,hLoad,_,hRead,hHeaders,_⟩ := GeneralPaperStoredChildRead.record_child model A start 32 installed
    (GeneralPaperStoredDominantCursor.schema model S A chosen row) (GeneralPaperStoredDominantCursor.child model S A chosen row)
    GeneralPaperStoredDominantCursor.fields hContract.2.1 hRoot ⟨0,by decide⟩
  let child := GeneralPaperStoredDominantCursor.child model S A chosen row .row fieldStart
  let loaded := GeneralPaperStoredScalarRead.atRoot installed child.root.reference
  change (GeneralPaperStoredChildRead.load model A installed 0 0).1 = some (⟨A,loaded⟩ : Child) at hLoad
  have hChildContract : Contract model A loaded (GeneralPaperStoredDominantCursor.expected model S A chosen row start) := hContract
  have hHeader := hHeaders _ (List.mem_singleton_self _)
  obtain ⟨hValues,hCount,_⟩ := GeneralPaperStoredReadStreamSources.rational_array model S A fieldStart loaded _ hChildContract
    (GeneralPaperStoredDominantCursor.rowTable row) hRead hHeader rfl
  refine ⟨child.root.reference,?_,?_,?_⟩
  · simp only [run,hLoad,hValues,PaperListReferenceArray.data,Array.toArray_toList]
    rfl
  · simp only [run,hLoad,hValues,hCount]
  · simp only [run,hLoad,hValues]
    rfl

end Blotto.GeneralPaperStoredDominantEmission
