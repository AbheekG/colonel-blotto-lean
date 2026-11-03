import Blotto.GeneralPaperStoredSelectedExt

/-! One actual initializer/copied-source preparation feeds one actual
selected directory constructor. The returned memory/root draws through the
stored marker; complete preparation work is attached without rerunning a pass. -/
namespace Blotto.GeneralPaperStoredSelectedPipeline
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperEqualInputDomain (Input word)
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 8192

def width (model : RationalCostModel) (A K : ℕ) (p : Input model) : ℕ :=
  (GeneralPaperEqualCopiedPipeline.run model A K p).1.address

def run (model : RationalCostModel) (A K : ℕ) (p : Input model) : Option (Installed (width model A K p)) × ℕ :=
  let prepared := GeneralPaperEqualCopiedPipeline.run model A K p
  let actual := GeneralPaperStoredSelectedConstruction.run model (word K p) prepared.1
  match actual.1 with
  | none => (none,prepared.2 + actual.2 + 64 * (word K p + prepared.1.address + 1))
  | some output =>
    let finished := GeneralPaperSamplerRecordInstallation.attach (word K p) prepared.1.address prepared.2 output
    (some finished,finished.work)

theorem source (model : RationalCostModel) (A K : ℕ) (p : Input model) :
    ∃ returned : Installed (width model A K p),(run model A K p).1 = some returned ∧
      returned.work = (run model A K p).2 ∧
      GeneralPaperStoredSelectedDraw.Refines model (width model A K p) returned
        (GeneralPaperEqualCopiedPipeline.run model A K p).1.branch := by
  let prepared := GeneralPaperEqualCopiedPipeline.run model A K p
  obtain ⟨inner,hBuilt,_,_⟩ := GeneralPaperStoredSelectedConstruction.source model (word K p) (word K p)
    p.k p.values p.selector p.correct p.budget prepared.1
  have hRefines := GeneralPaperStoredSelectedDraw.every_returned model (word K p) (word K p)
    p.k p.values p.selector p.correct p.budget prepared.1 inner hBuilt
  let output := GeneralPaperSamplerRecordInstallation.attach (word K p) prepared.1.address prepared.2 inner
  refine ⟨output,?_,?_,GeneralPaperStoredSelectedExt.attach model (word K p) prepared.1.address prepared.2 inner prepared.1.branch hRefines⟩
  · simp only [run,prepared,hBuilt,output]
  · simp only [run,prepared,hBuilt,output]

theorem every_returned (model : RationalCostModel) (A K : ℕ) (p : Input model)
    (returned : Installed (width model A K p)) (hReturn : (run model A K p).1 = some returned) :
    GeneralPaperStoredSelectedDraw.Refines model (width model A K p) returned
      (GeneralPaperEqualCopiedPipeline.run model A K p).1.branch := by
  obtain ⟨actual,hActual,_,hRefines⟩ := source model A K p
  have hEq : actual = returned := Option.some.inj (hActual.symm.trans hReturn)
  rw [← hEq]
  exact hRefines

theorem every_returned_work (model : RationalCostModel) (A K : ℕ) (p : Input model)
    (returned : Installed (width model A K p)) (hReturn : (run model A K p).1 = some returned) :
    returned.work = (run model A K p).2 := by
  obtain ⟨actual,hActual,hWork,_⟩ := source model A K p
  have hEq : actual = returned := Option.some.inj (hActual.symm.trans hReturn)
  rw [← hEq]
  exact hWork

theorem law (model : RationalCostModel) (A K : ℕ) (p : Input model)
    (returned : Installed (width model A K p)) (hReturn : (run model A K p).1 = some returned) :
    GeneralPaperStoredSelectedLaw.outputLaw model (width model A K p) returned
      (GeneralPaperEqualCopiedPipeline.run model A K p).1.branch =
      GeneralPaperEqualSelectedSampler.outputLaw model (GeneralPaperEqualCopiedPipeline.run model A K p).1 :=
  GeneralPaperStoredSelectedLaw.output_law_source model (width model A K p) returned _
    (every_returned model A K p returned hReturn)

theorem epsilon (model : RationalCostModel) (A K : ℕ) (p : Input model)
    (hOne : GeneralPaperEqualInputHeadline.epsilon p < 1) (hBudget : 0 < p.budget)
    (returned : Installed (width model A K p)) (hReturn : (run model A K p).1 = some returned) :
    let μ := GeneralPaperStoredSelectedLaw.outputLaw model (width model A K p) returned
      (GeneralPaperEqualCopiedPipeline.run model A K p).1.branch
    Supported (p.budget : ℝ) μ ∧ regret p.selector.values (p.budget : ℝ) μ μ ≤
      (GeneralPaperEqualInputHeadline.epsilon p : ℝ) := by
  dsimp only
  rw [law model A K p returned hReturn]
  exact GeneralPaperEqualCopiedPipeline.epsilon model A K p hOne hBudget

theorem epsilon_constructed (model : RationalCostModel) (A K : ℕ) (p : Input model)
    (hOne : GeneralPaperEqualInputHeadline.epsilon p < 1) (hBudget : 0 < p.budget) :
    ∃ returned : Installed (width model A K p),(run model A K p).1 = some returned ∧
      returned.work = (run model A K p).2 ∧
      let μ := GeneralPaperStoredSelectedLaw.outputLaw model (width model A K p) returned
        (GeneralPaperEqualCopiedPipeline.run model A K p).1.branch
      Supported (p.budget : ℝ) μ ∧ regret p.selector.values (p.budget : ℝ) μ μ ≤
        (GeneralPaperEqualInputHeadline.epsilon p : ℝ) := by
  obtain ⟨returned,hReturn,hWork,_⟩ := source model A K p
  exact ⟨returned,hReturn,hWork,epsilon model A K p hOne hBudget returned hReturn⟩

end Blotto.GeneralPaperStoredSelectedPipeline
