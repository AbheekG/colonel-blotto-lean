import Blotto.GeneralPaperUnifiedDirectoryViews

/-! A concrete source-matrix constructor returns one address map and root.
The same actual return preserves the following descriptor stream, carries
its complete construction price, and recovers every source rational entry.
Only source data and actual allocated descriptors are execution inputs. -/
namespace Blotto.GeneralPaperUnifiedMatrixInstallation
open GeneralPaperFieldDirectory GeneralPaperSequentialLayout
open GeneralPaperUnifiedDirectoryInstallation (Installed view)
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 8192

def finish (model : RationalCostModel) (S A prefixWork : ℕ) (directory : Directory A) : Installed A :=
  let actual := GeneralPaperUnifiedDirectoryInstallation.install model S A directory
  ⟨actual.memory,actual.root,prefixWork + actual.work + 64 * (S + A + 1)⟩

structure Result (A : ℕ) where
  values : Option (Installed A)
  remaining : List (Region A)
  work : ℕ

def run {m r : ℕ} (model : RationalCostModel) (S A : ℕ) (source : FixedArrayTable r (FixedArrayTable m ℚ))
    (regions : List (Region A)) : Result A :=
  let parsed := GeneralPaperMatrixFieldCursor.run S A source regions
  match parsed.values with
  | none => ⟨none,parsed.remaining,parsed.work + 64 * (S + A + 1)⟩
  | some directory =>
    let actual := finish model S A parsed.work directory
    ⟨some actual,parsed.remaining,actual.work⟩

theorem on_parsed {m r : ℕ} (model : RationalCostModel) (S A : ℕ) (source : FixedArrayTable r (FixedArrayTable m ℚ))
    (regions : List (Region A)) (directory : Directory A)
    (hParsed : (GeneralPaperMatrixFieldCursor.run S A source regions).values = some directory) :
    (run model S A source regions).values = some (finish model S A (GeneralPaperMatrixFieldCursor.run S A source regions).work directory) ∧
      (run model S A source regions).remaining = (GeneralPaperMatrixFieldCursor.run S A source regions).remaining ∧
      (run model S A source regions).work = (finish model S A (GeneralPaperMatrixFieldCursor.run S A source regions).work directory).work := by
  simp only [run,hParsed,and_self]

theorem rational_refinement {m r : ℕ} (model : RationalCostModel) (S A start prefixWork : ℕ)
    (source : FixedArrayTable r (FixedArrayTable m ℚ)) (hA : 0 < A)
    (hCap : start + (GeneralPaperEqualMeasuredRetainedPlan.matrix model S A source).sizes.sum < 2 ^ A)
    (row column : ℕ) :
    GeneralPaperMatrixFieldRead.rational model A
      (view (finish model S A prefixWork (GeneralPaperMatrixFieldCursor.expected model S A start source))) row column =
      GeneralPaperMatrixFieldRead.rational model A
        (GeneralPaperMatrixFieldInstallation.finish model S A prefixWork (GeneralPaperMatrixFieldCursor.expected model S A start source)) row column := by
  have hSafe := (GeneralPaperMatrixFieldCursor.success model S A start source []).2.2
  have hCovered := GeneralPaperFieldDirectoryPartition.matrix model S A start source
  have hPos := GeneralPaperEqualMeasuredPlanPositive.matrix model S A source hA
  obtain ⟨hr,hp,hroot⟩ := GeneralPaperUnifiedDirectoryViews.views model S A start
    (GeneralPaperEqualMeasuredRetainedPlan.matrix model S A source)
    (GeneralPaperMatrixFieldCursor.expected model S A start source) hSafe hCovered hPos hA hCap
  exact GeneralPaperUnifiedDirectoryViews.rational_ext model A _ _ hr hp hroot row column

theorem matrix_prefix {m r : ℕ} (model : RationalCostModel) (S A start : ℕ) (source : FixedArrayTable r (FixedArrayTable m ℚ))
    (rest : List (Region A)) (hA : 0 < A)
    (hCap : start + (GeneralPaperEqualMeasuredRetainedPlan.matrix model S A source).sizes.sum < 2 ^ A) :
    let regions := (GeneralPaperMeasuredBlockLayout.run model S A start (GeneralPaperEqualMeasuredRetainedPlan.matrix model S A source)).1 ++ rest
    ∃ output : Installed A,(run model S A source regions).values = some output ∧
      (run model S A source regions).remaining = rest ∧ output.work = (run model S A source regions).work ∧
      output.root = (GeneralPaperScalarArrayFieldCursor.layoutHeader A start r).reference ∧
      ∀ i : Fin r,∀ j : Fin m,(GeneralPaperMatrixFieldRead.rational model A (view output) i.val j.val).1 = some ((source.read i).read j) := by
  dsimp only
  let regions := (GeneralPaperMeasuredBlockLayout.run model S A start (GeneralPaperEqualMeasuredRetainedPlan.matrix model S A source)).1 ++ rest
  let directory := GeneralPaperMatrixFieldCursor.expected model S A start source
  obtain ⟨hParsed,hRemaining,_⟩ := GeneralPaperMatrixFieldCursor.success model S A start source rest
  obtain ⟨hv,hr,hw⟩ := on_parsed model S A source regions directory hParsed
  refine ⟨_,hv,hr.trans hRemaining,hw.symm,?_,?_⟩
  · change directory.root.reference = _
    rw [GeneralPaperMatrixFieldCursor.root]
  · intro i j
    rw [rational_refinement model S A start (GeneralPaperMatrixFieldCursor.run S A source regions).work source hA hCap]
    exact GeneralPaperMatrixFieldRead.rational_source model S A start source hA hCap i j

theorem every_returned_read {m r : ℕ} (model : RationalCostModel) (S A start : ℕ) (source : FixedArrayTable r (FixedArrayTable m ℚ))
    (rest : List (Region A)) (hA : 0 < A)
    (hCap : start + (GeneralPaperEqualMeasuredRetainedPlan.matrix model S A source).sizes.sum < 2 ^ A)
    (returned : Installed A)
    (hReturn : (run model S A source
      ((GeneralPaperMeasuredBlockLayout.run model S A start (GeneralPaperEqualMeasuredRetainedPlan.matrix model S A source)).1 ++ rest)).values = some returned)
    (i : Fin r) (j : Fin m) :
    (GeneralPaperMatrixFieldRead.rational model A (view returned) i.val j.val).1 = some ((source.read i).read j) := by
  obtain ⟨output,hRun,_,_,_,hRead⟩ := matrix_prefix model S A start source rest hA hCap
  have hEq : output = returned := Option.some.inj (hRun.symm.trans hReturn)
  rw [← hEq]
  exact hRead i j

theorem rational_read_work {m r : ℕ} (model : RationalCostModel) (S A start prefixWork : ℕ)
    (source : FixedArrayTable r (FixedArrayTable m ℚ)) (hA : 0 < A)
    (hCap : start + (GeneralPaperEqualMeasuredRetainedPlan.matrix model S A source).sizes.sum < 2 ^ A) (i : Fin r) (j : Fin m) :
    let installed := view (finish model S A prefixWork (GeneralPaperMatrixFieldCursor.expected model S A start source))
    ∃ rowRoot : FixedBinaryWord A,(GeneralPaperMatrixFieldRead.rational model A installed i.val j.val).2 =
      (GeneralPaperMixedReferenceRegionProgram.read model A installed.references installed.root 64 i.val).2 +
      (GeneralPaperMixedReferenceRegionProgram.read model A installed.references rowRoot 64 j.val).2 +
      rationalWordWidth ((source.read i).read j) + 320 * A + 192 := by
  dsimp only
  obtain ⟨rowRoot,hWork⟩ := GeneralPaperMatrixFieldInstallation.rational_read_work model S A start prefixWork source hA hCap i j
  refine ⟨rowRoot,?_⟩
  rw [rational_refinement model S A start prefixWork source hA hCap]
  have hSafe := (GeneralPaperMatrixFieldCursor.success model S A start source []).2.2
  obtain ⟨hr,_,hroot⟩ := GeneralPaperUnifiedDirectoryViews.views model S A start
    (GeneralPaperEqualMeasuredRetainedPlan.matrix model S A source)
    (GeneralPaperMatrixFieldCursor.expected model S A start source) hSafe
    (GeneralPaperFieldDirectoryPartition.matrix model S A start source)
    (GeneralPaperEqualMeasuredPlanPositive.matrix model S A source hA) hA hCap
  change (GeneralPaperMatrixFieldRead.rational model A
    (GeneralPaperMatrixFieldInstallation.finish model S A prefixWork (GeneralPaperMatrixFieldCursor.expected model S A start source)) i.val j.val).2 =
      (GeneralPaperMixedReferenceRegionProgram.read model A
        (view (GeneralPaperUnifiedDirectoryInstallation.install model S A (GeneralPaperMatrixFieldCursor.expected model S A start source))).references
        (view (GeneralPaperUnifiedDirectoryInstallation.install model S A (GeneralPaperMatrixFieldCursor.expected model S A start source))).root 64 i.val).2 +
      (GeneralPaperMixedReferenceRegionProgram.read model A
        (view (GeneralPaperUnifiedDirectoryInstallation.install model S A (GeneralPaperMatrixFieldCursor.expected model S A start source))).references rowRoot 64 j.val).2 +
      rationalWordWidth ((source.read i).read j) + 320 * A + 192
  rw [hr,hroot]
  exact hWork

end Blotto.GeneralPaperUnifiedMatrixInstallation
