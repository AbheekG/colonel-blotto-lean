import Blotto.GeneralPaperRouteArrayRead

/-! One concrete route-array return joins extraction, installation, root,
suffix, complete construction work and every original source-indexed route.
The generic finish copies only returned metadata and records the prefix work. -/
namespace Blotto.GeneralPaperRouteArrayInstallation
open GeneralPaperSequentialLayout GeneralPaperFieldDirectory
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperUnifiedMatrixInstallation (finish Result)
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 8192

def run {n m : ℕ} (model : RationalCostModel) (S A : ℕ) (source : FixedArrayTable n (GroupRoute m))
    (regions : List (Region A)) : Result A :=
  let parsed := GeneralPaperRouteArrayCursor.run S A source regions
  match parsed.values with
  | none => ⟨none,parsed.remaining,parsed.work + 64 * (S + A + 1)⟩
  | some directory =>
    let actual := finish model S A parsed.work directory
    ⟨some actual,parsed.remaining,actual.work⟩

theorem on_parsed {n m : ℕ} (model : RationalCostModel) (S A : ℕ) (source : FixedArrayTable n (GroupRoute m))
    (regions : List (Region A)) (directory : Directory A)
    (hParsed : (GeneralPaperRouteArrayCursor.run S A source regions).values = some directory) :
    (run model S A source regions).values = some (finish model S A (GeneralPaperRouteArrayCursor.run S A source regions).work directory) ∧
      (run model S A source regions).remaining = (GeneralPaperRouteArrayCursor.run S A source regions).remaining ∧
      (run model S A source regions).work = (finish model S A (GeneralPaperRouteArrayCursor.run S A source regions).work directory).work := by
  simp only [run,hParsed,and_self]

theorem array_prefix {n m : ℕ} (model : RationalCostModel) (S A start : ℕ) (source : FixedArrayTable n (GroupRoute m))
    (rest : List (Region A)) (hA : 0 < A)
    (hCap : start + (GeneralPaperMeasuredArrayBlockPlan.array model S A (GeneralPaperEqualMeasuredLeafPlans.route model S A) source).sizes.sum < 2 ^ A) :
    let regions := (GeneralPaperMeasuredBlockLayout.run model S A start
      (GeneralPaperMeasuredArrayBlockPlan.array model S A (GeneralPaperEqualMeasuredLeafPlans.route model S A) source)).1 ++ rest
    ∃ output : Installed A,(run model S A source regions).values = some output ∧
      (run model S A source regions).remaining = rest ∧ output.work = (run model S A source regions).work ∧
      output.root = (GeneralPaperScalarArrayFieldCursor.layoutHeader A start n).reference ∧
      ∀ i : Fin n,(GeneralPaperRouteArrayRead.read model A output i.val).1 = some ((source.read i).1.map Fin.val,(source.read i).2) := by
  dsimp only
  let regions := (GeneralPaperMeasuredBlockLayout.run model S A start
    (GeneralPaperMeasuredArrayBlockPlan.array model S A (GeneralPaperEqualMeasuredLeafPlans.route model S A) source)).1 ++ rest
  let directory := GeneralPaperRouteArrayCursor.expected model S A start source
  obtain ⟨hParsed,hRemaining,_⟩ := GeneralPaperRouteArrayCursor.success model S A start source rest
  obtain ⟨hv,hr,hw⟩ := on_parsed model S A source regions directory hParsed
  refine ⟨_,hv,hr.trans hRemaining,hw.symm,?_,?_⟩
  · change directory.root.reference = _
    rw [GeneralPaperRouteArrayCursor.root]
  · intro i
    exact (GeneralPaperRouteArrayRead.source model S A start source hA hCap i).choose_spec.1

theorem every_returned_read {n m : ℕ} (model : RationalCostModel) (S A start : ℕ) (source : FixedArrayTable n (GroupRoute m))
    (rest : List (Region A)) (hA : 0 < A)
    (hCap : start + (GeneralPaperMeasuredArrayBlockPlan.array model S A (GeneralPaperEqualMeasuredLeafPlans.route model S A) source).sizes.sum < 2 ^ A)
    (returned : Installed A)
    (hReturn : (run model S A source
      ((GeneralPaperMeasuredBlockLayout.run model S A start
        (GeneralPaperMeasuredArrayBlockPlan.array model S A (GeneralPaperEqualMeasuredLeafPlans.route model S A) source)).1 ++ rest)).values = some returned)
    (i : Fin n) :
    (GeneralPaperRouteArrayRead.read model A returned i.val).1 = some ((source.read i).1.map Fin.val,(source.read i).2) := by
  obtain ⟨output,hRun,_,_,_,hRead⟩ := array_prefix model S A start source rest hA hCap
  have hEq : output = returned := Option.some.inj (hRun.symm.trans hReturn)
  rw [← hEq]
  exact hRead i

end Blotto.GeneralPaperRouteArrayInstallation
