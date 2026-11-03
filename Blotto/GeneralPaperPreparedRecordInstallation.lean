import Blotto.GeneralPaperDirectoryRecordRead

/-! One prepared-cache constructor returns the installed heterogeneous record.
The same return preserves the following region stream and reads the original
budget and every child root. This is still a component of the full sampler. -/
namespace Blotto.GeneralPaperPreparedRecordInstallation
open GeneralPaperSequentialLayout GeneralPaperFieldDirectory GeneralPaperRetainedScalarValue
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperUnifiedMatrixInstallation (finish Result)
open GeneralPaperUnifiedFieldValue
open GeneralPaperMixedReferenceMemory (Word)
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 8192
variable {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}

def budget (model : RationalCostModel) (A : ℕ) (installed : Installed A) : Option ℚ × ℕ :=
  let actual := GeneralPaperRecordScalarRead.read model A installed 4
  match actual.1 with
  | some (.rational value) => (some value,actual.2 + rationalWordWidth value + 64 * A + 64)
  | _ => (none,actual.2 + 64 * A + 64)

theorem budget_source (model : RationalCostModel) (S A start : ℕ) (source : GeneralPaperEqualPreparedCache.Prepared G l)
    (hA : 0 < A) (hCap : start + (GeneralPaperEqualMeasuredRetainedPlan.prepared model S A source).sizes.sum < 2 ^ A) :
    let installed := GeneralPaperUnifiedDirectoryInstallation.install model S A (GeneralPaperPreparedRecordCursor.expected model S A source start)
    (budget model A installed).1 = some source.budget ∧ (budget model A installed).2 =
      (GeneralPaperMixedReferenceRegionProgram.read model A (referenceMemory installed.memory) installed.root 0 4).2 +
      2 * rationalWordWidth source.budget + 256 * A + 192 := by
  dsimp only
  obtain ⟨hr,hw⟩ := GeneralPaperDirectoryRecordRead.prepared_budget model S A start source hA hCap
  simp only [budget,hr]
  constructor
  · exact True.intro
  · rw [hw]
    ring

def run (model : RationalCostModel) (S A : ℕ) (source : GeneralPaperEqualPreparedCache.Prepared G l)
    (regions : List (Region A)) : Result A :=
  let parsed := GeneralPaperPreparedRecordCursor.run S A source regions
  match parsed.values with
  | none => ⟨none,parsed.remaining,parsed.work + 64 * (S + A + 1)⟩
  | some directory =>
    let actual := finish model S A parsed.work directory
    ⟨some actual,parsed.remaining,actual.work⟩

theorem on_parsed (model : RationalCostModel) (S A : ℕ) (source : GeneralPaperEqualPreparedCache.Prepared G l)
    (regions : List (Region A)) (directory : Directory A)
    (hParsed : (GeneralPaperPreparedRecordCursor.run S A source regions).values = some directory) :
    (run model S A source regions).values = some (finish model S A (GeneralPaperPreparedRecordCursor.run S A source regions).work directory) ∧
      (run model S A source regions).remaining = (GeneralPaperPreparedRecordCursor.run S A source regions).remaining ∧
      (run model S A source regions).work = (finish model S A (GeneralPaperPreparedRecordCursor.run S A source regions).work directory).work := by
  simp only [run,hParsed,and_self]

theorem record_prefix (model : RationalCostModel) (S A start : ℕ) (source : GeneralPaperEqualPreparedCache.Prepared G l)
    (rest : List (Region A)) (hA : 0 < A)
    (hCap : start + (GeneralPaperEqualMeasuredRetainedPlan.prepared model S A source).sizes.sum < 2 ^ A) :
    let regions := (GeneralPaperMeasuredBlockLayout.run model S A start (GeneralPaperEqualMeasuredRetainedPlan.prepared model S A source)).1 ++ rest
    ∃ output : Installed A,(run model S A source regions).values = some output ∧
      (run model S A source regions).remaining = rest ∧ output.work = (run model S A source regions).work ∧
      output.root = (GeneralPaperPreparedRecordCursor.expected model S A source start).root.reference ∧
      (budget model A output).1 = some source.budget ∧
      ∀ index : Fin GeneralPaperPreparedRecordCursor.fields.length,∃ fieldStart,
        (GeneralPaperMixedReferenceRegionProgram.read model A (referenceMemory output.memory) output.root 0 index.val).1 =
          some (⟨A,(GeneralPaperPreparedRecordCursor.child model S A source (GeneralPaperPreparedRecordCursor.fields[index.val]) fieldStart).root.reference⟩ : Word) := by
  dsimp only
  let regions := (GeneralPaperMeasuredBlockLayout.run model S A start (GeneralPaperEqualMeasuredRetainedPlan.prepared model S A source)).1 ++ rest
  let directory := GeneralPaperPreparedRecordCursor.expected model S A source start
  obtain ⟨hParsed,hRemaining,_,_⟩ := GeneralPaperPreparedRecordCursor.success model S A start source rest
  obtain ⟨hv,hr,hw⟩ := on_parsed model S A source regions directory hParsed
  refine ⟨_,hv,hr.trans hRemaining,hw.symm,rfl,(budget_source model S A start source hA hCap).1,?_⟩
  intro index
  obtain ⟨fieldStart,hRead,_⟩ := GeneralPaperDirectoryRecordRead.prepared_child model S A start source hA hCap index
  exact ⟨fieldStart,hRead⟩

theorem every_returned_budget (model : RationalCostModel) (S A start : ℕ) (source : GeneralPaperEqualPreparedCache.Prepared G l)
    (rest : List (Region A)) (hA : 0 < A)
    (hCap : start + (GeneralPaperEqualMeasuredRetainedPlan.prepared model S A source).sizes.sum < 2 ^ A)
    (returned : Installed A)
    (hReturn : (run model S A source
      ((GeneralPaperMeasuredBlockLayout.run model S A start (GeneralPaperEqualMeasuredRetainedPlan.prepared model S A source)).1 ++ rest)).values = some returned) :
    (budget model A returned).1 = some source.budget := by
  obtain ⟨output,hRun,_,_,_,hBudget,_⟩ := record_prefix model S A start source rest hA hCap
  have hEq : output = returned := Option.some.inj (hRun.symm.trans hReturn)
  rw [← hEq]
  exact hBudget

end Blotto.GeneralPaperPreparedRecordInstallation
