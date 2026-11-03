import Blotto.GeneralPaperStoredDominantCursor

/-! Count-initialize and install the entire dominant directory once.
Source extraction, unchanged owners, stored counts and every old readback
share the actual returned memory, root, continuation and construction work. -/
namespace Blotto.GeneralPaperStoredDominantInstallation
open GeneralPaperFieldDirectory GeneralPaperSequentialLayout
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperUnifiedMatrixInstallation (Result)
open GeneralPaperHeaderCountInstallation (Contract)
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 8192

def run {n : ℕ} (model : RationalCostModel) (S A chosen : ℕ) (source : RationalResourceArray n)
    (regions : List (Region A)) : Result A :=
  let parsed := GeneralPaperStoredDominantCursor.run S A chosen source regions
  match parsed.values with
  | none => ⟨none,parsed.remaining,parsed.work + 64 * (S + A + 1)⟩
  | some directory =>
    let output := GeneralPaperHeaderCountInstallation.finish model S A parsed.work directory
    ⟨some output,parsed.remaining,output.work⟩

theorem source {n : ℕ} (model : RationalCostModel) (S A start chosen : ℕ) (row : RationalResourceArray n)
    (rest : List (Region A)) (hA : 0 < A)
    (hCap : start + (GeneralPaperStoredDominantCursor.plan model S A chosen row).sizes.sum < 2 ^ A) :
    let regions := (GeneralPaperMeasuredBlockLayout.run model S A start (GeneralPaperStoredDominantCursor.plan model S A chosen row)).1 ++ rest
    ∃ output : Installed A,(run model S A chosen row regions).values = some output ∧
      (run model S A chosen row regions).remaining = rest ∧ output.work = (run model S A chosen row regions).work ∧
      output.root = (GeneralPaperStoredDominantCursor.expected model S A chosen row start).root.reference ∧
      Contract model A output (GeneralPaperStoredDominantCursor.expected model S A chosen row start) := by
  dsimp only
  let regions := (GeneralPaperMeasuredBlockLayout.run model S A start (GeneralPaperStoredDominantCursor.plan model S A chosen row)).1 ++ rest
  let directory := GeneralPaperStoredDominantCursor.expected model S A chosen row start
  let prefixWork := (GeneralPaperStoredDominantCursor.run S A chosen row regions).work
  let output := GeneralPaperHeaderCountInstallation.finish model S A prefixWork directory
  obtain ⟨hParsed,hRemaining,hs,hc⟩ := GeneralPaperStoredDominantCursor.success model S A start chosen row rest
  refine ⟨output,?_,?_,?_,GeneralPaperHeaderCountInstallation.root model S A prefixWork directory,?_⟩
  · simp only [run,hParsed,output,prefixWork,directory,regions]
  · simp only [run,hParsed,hRemaining]
  · simp only [run,hParsed,output,prefixWork,directory,regions]
  · exact GeneralPaperHeaderCountInstallation.contract model S A start prefixWork _ directory hs hc
      (GeneralPaperStoredDominantCursor.positive model S A chosen row hA) hA hCap

end Blotto.GeneralPaperStoredDominantInstallation
