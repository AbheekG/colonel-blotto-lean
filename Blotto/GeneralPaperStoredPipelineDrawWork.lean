import Blotto.GeneralPaperStoredDrawWorkExt

/-! Every initialized/copied pipeline return carries the complete common
expected draw cost. Attaching preparation work changes no draw execution;
the identical majorant has the native paper-input growth rate. -/
namespace Blotto.GeneralPaperStoredPipelineDrawWork
open MeasureTheory
open scoped ENNReal
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperEqualInputDomain (Input word)
open GeneralPaperUniformResourceGrowth
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192

def majorant (model : RationalCostModel) (A K : ℕ) (p : Input model) : ℕ :=
  GeneralPaperStoredSelectedReturnWork.bound model (GeneralPaperStoredSelectedPipeline.width model A K p) p.n p.k (rationalWordWidth p.budget)

theorem width_independent (model : RationalCostModel) (A B K : ℕ) (p : Input model) :
    GeneralPaperStoredSelectedPipeline.width model A K p = GeneralPaperStoredSelectedPipeline.width model B K p := by
  unfold GeneralPaperStoredSelectedPipeline.width
  rw [GeneralPaperEqualCopiedPipeline.data model A K p,GeneralPaperEqualCopiedPipeline.data model B K p]

theorem majorant_independent (model : RationalCostModel) (A B K : ℕ) (p : Input model) :
    majorant model A K p = majorant model B K p := by
  unfold majorant
  rw [width_independent model A B K p]

theorem expected_work (model : RationalCostModel) (A K : ℕ) (p : Input model)
    (returned : Installed (GeneralPaperStoredSelectedPipeline.width model A K p))
    (hReturn : (GeneralPaperStoredSelectedPipeline.run model A K p).1 = some returned) :
    (∫⁻ trace, ((GeneralPaperStoredSelectedLaw.observed model (GeneralPaperStoredSelectedPipeline.width model A K p) returned
        (GeneralPaperEqualCopiedPipeline.run model A K p).1.branch trace).work : ℝ≥0∞)
      ∂(GeneralPaperEqualBitBranchDraw.traceLaw (GeneralPaperEqualCopiedPipeline.run model A K p).1.branch :
        Measure (GeneralPaperEqualBitBranchDraw.Trace (GeneralPaperEqualCopiedPipeline.run model A K p).1.branch))) ≤
      (majorant model A K p : ℝ≥0∞) := by
  dsimp only [GeneralPaperStoredSelectedPipeline.run] at hReturn
  cases hBuilt : (GeneralPaperStoredSelectedConstruction.run model (word K p) (GeneralPaperEqualCopiedPipeline.run model A K p).1).1 with
  | none => simp only [hBuilt] at hReturn; cases hReturn
  | some inner =>
    simp only [hBuilt] at hReturn
    rw [← Option.some.inj hReturn]
    have hExt := GeneralPaperStoredDrawWorkExt.expected_ext model (GeneralPaperStoredSelectedPipeline.width model A K p)
      (GeneralPaperSamplerRecordInstallation.attach (word K p) (GeneralPaperEqualCopiedPipeline.run model A K p).1.address
        (GeneralPaperEqualCopiedPipeline.run model A K p).2 inner) inner rfl rfl (GeneralPaperEqualCopiedPipeline.run model A K p).1.branch
    rw [hExt]
    exact GeneralPaperStoredSelectedReturnWork.expected_work model (word K p) (word K p) p.k p.values p.selector p.correct p.budget
      (GeneralPaperEqualCopiedPipeline.run model A K p).1 inner hBuilt

theorem rate (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) (A K : ℕ) :
    Bound (majorant model A K) GeneralPaperStoredSelectedReturnWork.inputScale GeneralPaperStoredNativeReadRates.drawLog :=
  GeneralPaperStoredSelectedReturnWork.input_rate model hFast A K

end Blotto.GeneralPaperStoredPipelineDrawWork
