import Blotto.GeneralPaperStoredDominantOuterDraw

/-! The dominant source-only constructor computes both pools once, installs
the counted inner row/label/record once and extends that very memory with
the unchanged outer fields. Its return supports actual full-row drawing. -/
namespace Blotto.GeneralPaperStoredDominantOuterConstruction
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperEqualOuterFieldLayout
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192

def layout {n : ℕ} (model : RationalCostModel) (S A chosen : ℕ) (row : RationalResourceArray n) :=
  GeneralPaperMeasuredTwoPoolLayout.run model S A A (GeneralPaperStoredDominantCursor.plan model S A chosen row)
    (GeneralPaperEqualMeasuredSelectedPlan.header model S A)

def run {n : ℕ} (model : RationalCostModel) (S A chosen : ℕ) (row : RationalResourceArray n) : GeneralPaperStoredGroupedOuterConstruction.Result A A :=
  let regions := layout model S A chosen row
  let inner := GeneralPaperStoredDominantInstallation.run model S A chosen row regions.inner
  let fields := extract S A regions.outer
  match inner.values,fields.1 with
  | some actualInner,some actualFields =>
    let outer := GeneralPaperStoredOuterAttachment.finish model S A A (regions.work + fields.2) actualFields actualInner 0
    ⟨some outer,inner.remaining,outer.work⟩
  | _,_ => ⟨none,inner.remaining,regions.work + inner.work + fields.2 + 128 * (S + A + A + 1)⟩

theorem fields_source {n : ℕ} (model : RationalCostModel) (S A chosen : ℕ) (row : RationalResourceArray n) :
    (extract S A (layout model S A chosen row).outer).1 = some (canonical A (layout model S A chosen row).boundary) :=
  GeneralPaperEqualOuterFieldLayout.extracted model S A _

theorem source {n : ℕ} (model : RationalCostModel) (S A chosen : ℕ) (row : RationalResourceArray n)
    (hA : 0 < A) (hInnerCap : (GeneralPaperStoredDominantCursor.plan model S A chosen row).sizes.sum < 2 ^ A)
    (hOuterCap : (GeneralPaperStoredDominantCursor.plan model S A chosen row).sizes.sum +
      (GeneralPaperEqualMeasuredSelectedPlan.header model S A).sizes.sum < 2 ^ A) :
    ∃ returned : Installed A,(run model S A chosen row).values = some returned ∧
      (run model S A chosen row).remaining = [] ∧ returned.work = (run model S A chosen row).work ∧
      (GeneralPaperStoredDominantOuterDraw.run model A returned).values = some row.data ∧
      (GeneralPaperStoredDominantOuterDraw.run model A returned).count = n := by
  obtain ⟨inner,hInner,hRemaining,_,hRoot,hContract⟩ := GeneralPaperStoredDominantInstallation.source model S A 0 chosen row [] hA
    (by simpa only [Nat.zero_add] using hInnerCap)
  simp only [List.append_nil] at hInner hRemaining
  have hInnerActual : (GeneralPaperStoredDominantInstallation.run model S A chosen row (layout model S A chosen row).inner).values = some inner := hInner
  have hRemainingActual : (GeneralPaperStoredDominantInstallation.run model S A chosen row (layout model S A chosen row).inner).remaining = [] := hRemaining
  have hBoundary : (layout model S A chosen row).boundary = (GeneralPaperStoredDominantCursor.plan model S A chosen row).sizes.sum :=
    GeneralPaperMeasuredTwoPoolLayout.boundary model S A A _ _
  let outer := GeneralPaperStoredOuterAttachment.finish model S A A
    ((layout model S A chosen row).work + (extract S A (layout model S A chosen row).outer).2)
    (canonical A (layout model S A chosen row).boundary) inner 0
  have hReturn : (run model S A chosen row).values = some outer := by simp only [run,hInnerActual,fields_source,outer]
  have hRest : (run model S A chosen row).remaining = [] := by simp only [run,hInnerActual,fields_source,hRemainingActual]
  have hWork : outer.work = (run model S A chosen row).work := by simp only [run,hInnerActual,fields_source,outer]
  refine ⟨outer,hReturn,hRest,hWork,?_⟩
  have hDraw := GeneralPaperStoredDominantOuterDraw.attached_source model S A
    ((layout model S A chosen row).work + (extract S A (layout model S A chosen row).outer).2)
    chosen row inner hContract hRoot hA hInnerCap hOuterCap
  simpa only [outer,hBoundary] using hDraw

theorem every_returned {n : ℕ} (model : RationalCostModel) (S A chosen : ℕ) (row : RationalResourceArray n)
    (hA : 0 < A) (hInnerCap : (GeneralPaperStoredDominantCursor.plan model S A chosen row).sizes.sum < 2 ^ A)
    (hOuterCap : (GeneralPaperStoredDominantCursor.plan model S A chosen row).sizes.sum +
      (GeneralPaperEqualMeasuredSelectedPlan.header model S A).sizes.sum < 2 ^ A)
    (returned : Installed A) (hReturn : (run model S A chosen row).values = some returned) :
    (GeneralPaperStoredDominantOuterDraw.run model A returned).values = some row.data ∧
      (GeneralPaperStoredDominantOuterDraw.run model A returned).count = n := by
  obtain ⟨actual,hActual,_,_,hDraw⟩ := source model S A chosen row hA hInnerCap hOuterCap
  have hEq : actual = returned := Option.some.inj (hActual.symm.trans hReturn)
  rw [← hEq]
  exact hDraw

end Blotto.GeneralPaperStoredDominantOuterConstruction
