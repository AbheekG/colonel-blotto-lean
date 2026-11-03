import Blotto.GeneralPaperStoredPipelineDrawWork

/-! The parsed-exponent continuation carries complete common draw work.
Only one reference/dispatch/copy/construction follows parsing; no second
accuracy preparation is executed to obtain the resource theorem. -/
namespace Blotto.GeneralPaperStoredParsedDrawWork
open MeasureTheory
open scoped ENNReal
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperBinaryAccuracy (Parsed)
open GeneralPaperStoredParsedPreparation (width prepare input)
open GeneralPaperUniformResourceGrowth
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192

def majorant {n : ℕ} (model : RationalCostModel) (A K : ℕ) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j) (budget : ℚ) (parsed : Parsed) : ℕ :=
  GeneralPaperStoredSelectedReturnWork.bound model (width model A K values v hv budget parsed) n parsed.exponent (rationalWordWidth budget)

theorem majorant_data {n : ℕ} (model : RationalCostModel) (A K : ℕ) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j) (budget : ℚ) (parsed : Parsed) :
    majorant model A K values v hv budget parsed =
      GeneralPaperStoredPipelineDrawWork.majorant model A K (input model values v hv budget parsed) := by
  unfold majorant width
  rw [GeneralPaperStoredParsedPreparation.prepared_data]
  rfl

theorem expected_work {n : ℕ} (model : RationalCostModel) (A K : ℕ) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j) (budget : ℚ) (parsed : Parsed)
    (returned : Installed (width model A K values v hv budget parsed))
    (hReturn : (GeneralPaperStoredParsedPreparation.run model A K values v hv budget parsed).1 = some returned) :
    (∫⁻ trace, ((GeneralPaperStoredSelectedLaw.observed model (width model A K values v hv budget parsed) returned
        (prepare model A K values v hv budget parsed).1.branch trace).work : ℝ≥0∞)
      ∂(GeneralPaperEqualBitBranchDraw.traceLaw (prepare model A K values v hv budget parsed).1.branch :
        Measure (GeneralPaperEqualBitBranchDraw.Trace (prepare model A K values v hv budget parsed).1.branch))) ≤
      (majorant model A K values v hv budget parsed : ℝ≥0∞) := by
  let W := GeneralPaperEqualInputDomain.word K (input model values v hv budget parsed)
  dsimp only [GeneralPaperStoredParsedPreparation.run] at hReturn
  cases hBuilt : (GeneralPaperStoredSelectedConstruction.run model W (prepare model A K values v hv budget parsed).1).1 with
  | none =>
    dsimp only [W] at hBuilt
    simp only [hBuilt] at hReturn
    cases hReturn
  | some inner =>
    dsimp only [W] at hBuilt
    simp only [hBuilt] at hReturn
    rw [← Option.some.inj hReturn]
    have hExt := GeneralPaperStoredDrawWorkExt.expected_ext model (width model A K values v hv budget parsed)
      (GeneralPaperSamplerRecordInstallation.attach W (prepare model A K values v hv budget parsed).1.address
        (prepare model A K values v hv budget parsed).2 inner) inner rfl rfl (prepare model A K values v hv budget parsed).1.branch
    dsimp only [W] at hExt
    rw [hExt]
    exact GeneralPaperStoredSelectedReturnWork.expected_work model W W parsed.exponent values v hv budget
      (prepare model A K values v hv budget parsed).1 inner hBuilt

theorem rate {n : ℕ} (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) (A K : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j) (budget : ℚ) :
    Bound (majorant model A K values v hv budget)
      (fun parsed => GeneralPaperStoredSelectedReturnWork.inputScale (input model values v hv budget parsed))
      (fun parsed => GeneralPaperStoredNativeReadRates.drawLog (input model values v hv budget parsed)) := by
  obtain ⟨C,d,hC⟩ := GeneralPaperStoredPipelineDrawWork.rate model hFast A K
  refine ⟨C,d,fun parsed => ?_⟩
  rw [majorant_data]
  exact hC (input model values v hv budget parsed)

end Blotto.GeneralPaperStoredParsedDrawWork
