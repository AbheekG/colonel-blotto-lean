import Blotto.GeneralPaperMatrixFieldRead

/-! One matrix constructor joins concrete row parsing, complete directory
installation and source-indexed rational reads on the same actual return.
All later region descriptors remain untouched. No supplied directory, size,
root, capacity or decoded target is an execution input. -/
namespace Blotto.GeneralPaperMatrixFieldInstallation
open GeneralPaperFieldDirectory GeneralPaperSequentialLayout
open GeneralPaperFieldDirectoryInstallation (Installed)
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192

def finish (model : RationalCostModel) (S A prefixWork : ℕ) (directory : Directory A) : Installed A :=
  let actual := GeneralPaperFieldDirectoryInstallation.install model S A directory
  ⟨actual.references,actual.payloads,actual.root,prefixWork + actual.work + 64 * (S + A + 1)⟩

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

theorem matrix_prefix {m r : ℕ} (model : RationalCostModel) (S A start : ℕ) (source : FixedArrayTable r (FixedArrayTable m ℚ))
    (rest : List (Region A)) (hA : 0 < A)
    (hCap : start + (GeneralPaperEqualMeasuredRetainedPlan.matrix model S A source).sizes.sum < 2 ^ A) :
    let regions := (GeneralPaperMeasuredBlockLayout.run model S A start (GeneralPaperEqualMeasuredRetainedPlan.matrix model S A source)).1 ++ rest
    ∃ output : Installed A,(run model S A source regions).values = some output ∧
      (run model S A source regions).remaining = rest ∧ output.work = (run model S A source regions).work ∧
      output.root = (GeneralPaperScalarArrayFieldCursor.layoutHeader A start r).reference ∧
      ∀ i : Fin r,∀ j : Fin m,(GeneralPaperMatrixFieldRead.rational model A output i.val j.val).1 = some ((source.read i).read j) := by
  dsimp only
  let regions := (GeneralPaperMeasuredBlockLayout.run model S A start (GeneralPaperEqualMeasuredRetainedPlan.matrix model S A source)).1 ++ rest
  let directory := GeneralPaperMatrixFieldCursor.expected model S A start source
  obtain ⟨hParsed,hRemaining,_⟩ := GeneralPaperMatrixFieldCursor.success model S A start source rest
  obtain ⟨hv,hr,hw⟩ := on_parsed model S A source regions directory hParsed
  refine ⟨_,hv,hr.trans hRemaining,hw.symm,?_,?_⟩
  · change directory.root.reference = _
    rw [GeneralPaperMatrixFieldCursor.root]
  · intro i j
    exact GeneralPaperMatrixFieldRead.rational_source model S A start source hA hCap i j

theorem every_returned_read {m r : ℕ} (model : RationalCostModel) (S A start : ℕ) (source : FixedArrayTable r (FixedArrayTable m ℚ))
    (rest : List (Region A)) (hA : 0 < A)
    (hCap : start + (GeneralPaperEqualMeasuredRetainedPlan.matrix model S A source).sizes.sum < 2 ^ A)
    (returned : Installed A)
    (hReturn : (run model S A source
      ((GeneralPaperMeasuredBlockLayout.run model S A start (GeneralPaperEqualMeasuredRetainedPlan.matrix model S A source)).1 ++ rest)).values = some returned)
    (i : Fin r) (j : Fin m) :
    (GeneralPaperMatrixFieldRead.rational model A returned i.val j.val).1 = some ((source.read i).read j) := by
  obtain ⟨output,hRun,_,_,_,hRead⟩ := matrix_prefix model S A start source rest hA hCap
  have hEq : output = returned := Option.some.inj (hRun.symm.trans hReturn)
  rw [← hEq]
  exact hRead i j

theorem rational_read_work {m r : ℕ} (model : RationalCostModel) (S A start prefixWork : ℕ)
    (source : FixedArrayTable r (FixedArrayTable m ℚ)) (hA : 0 < A)
    (hCap : start + (GeneralPaperEqualMeasuredRetainedPlan.matrix model S A source).sizes.sum < 2 ^ A) (i : Fin r) (j : Fin m) :
    let installed := finish model S A prefixWork (GeneralPaperMatrixFieldCursor.expected model S A start source)
    ∃ rowRoot : FixedBinaryWord A,(GeneralPaperMatrixFieldRead.rational model A installed i.val j.val).2 =
      (GeneralPaperMixedReferenceRegionProgram.read model A installed.references installed.root 64 i.val).2 +
      (GeneralPaperMixedReferenceRegionProgram.read model A installed.references rowRoot 64 j.val).2 +
      rationalWordWidth ((source.read i).read j) + 320 * A + 192 := by
  dsimp only
  obtain ⟨rowRoot,hRead,hWork⟩ := GeneralPaperMatrixFieldRead.source model S A start source hA hCap i j
  refine ⟨rowRoot,?_⟩
  dsimp only [finish]
  change (GeneralPaperMatrixFieldRead.rational model A (GeneralPaperFieldDirectoryInstallation.install model S A
    (GeneralPaperMatrixFieldCursor.expected model S A start source)) i.val j.val).2 = _
  simp only [GeneralPaperMatrixFieldRead.rational,hRead]
  rw [hWork]
  ring

end Blotto.GeneralPaperMatrixFieldInstallation
