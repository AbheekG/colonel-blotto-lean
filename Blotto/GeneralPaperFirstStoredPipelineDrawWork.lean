import Blotto.GeneralPaperFirstStoredReturnDrawWork

/-! Complete expected work of the actual corrected direct installed
pipeline. Result attachment preserves its stored draw execution exactly. -/
namespace Blotto.GeneralPaperFirstStoredPipelineDrawWork
open MeasureTheory
open scoped ENNReal
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperEqualInputDomain (Input word)
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

def majorant (model : RationalCostModel) (A K : ℕ) (p : Input model) : ℕ :=
  GeneralPaperFirstStoredReturnDrawWork.bound model (GeneralPaperFirstStoredPipeline.width model A K p) p.n p.k (rationalWordWidth p.budget)

theorem width_independent (model : RationalCostModel) (A B K : ℕ) (p : Input model) :
    GeneralPaperFirstStoredPipeline.width model A K p = GeneralPaperFirstStoredPipeline.width model B K p := by
  unfold GeneralPaperFirstStoredPipeline.width
  rw [GeneralPaperEqualFirstInputPipeline.data model A K p,GeneralPaperEqualFirstInputPipeline.data model B K p]

theorem majorant_independent (model : RationalCostModel) (A B K : ℕ) (p : Input model) :
    majorant model A K p = majorant model B K p := by
  unfold majorant
  rw [width_independent model A B K p]

theorem expected_work (model : RationalCostModel) (A K : ℕ) (p : Input model)
    (returned : Installed (GeneralPaperFirstStoredPipeline.width model A K p))
    (hReturn : (GeneralPaperFirstStoredPipeline.run model A K p).1 = some returned) :
    (∫⁻ trace, ((GeneralPaperStoredSelectedLaw.observed model (GeneralPaperFirstStoredPipeline.width model A K p) returned
        (GeneralPaperEqualFirstInputPipeline.run model A K p).1.branch trace).work : ℝ≥0∞)
      ∂(GeneralPaperEqualBitBranchDraw.traceLaw (GeneralPaperEqualFirstInputPipeline.run model A K p).1.branch :
        Measure (GeneralPaperEqualBitBranchDraw.Trace (GeneralPaperEqualFirstInputPipeline.run model A K p).1.branch))) ≤
      (majorant model A K p : ℝ≥0∞) := by
  dsimp only [GeneralPaperFirstStoredPipeline.run] at hReturn
  cases hBuilt : (GeneralPaperStoredSelectedConstruction.run model (word K p) (GeneralPaperEqualFirstInputPipeline.run model A K p).1).1 with
  | none => simp only [hBuilt] at hReturn; cases hReturn
  | some inner =>
    simp only [hBuilt] at hReturn
    rw [← Option.some.inj hReturn]
    have hExt := GeneralPaperStoredDrawWorkExt.expected_ext model (GeneralPaperFirstStoredPipeline.width model A K p)
      (GeneralPaperSamplerRecordInstallation.attach (word K p) (GeneralPaperEqualFirstInputPipeline.run model A K p).1.address
        (GeneralPaperEqualFirstInputPipeline.run model A K p).2 inner) inner rfl rfl (GeneralPaperEqualFirstInputPipeline.run model A K p).1.branch
    rw [hExt]
    exact GeneralPaperFirstStoredReturnDrawWork.expected_work model (word K p) (word K p) p.k p.values p.selector p.correct p.budget
      (GeneralPaperEqualFirstInputPipeline.run model A K p).1 inner hBuilt


end Blotto.GeneralPaperFirstStoredPipelineDrawWork
