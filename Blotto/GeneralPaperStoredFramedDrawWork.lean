import Blotto.GeneralPaperStoredParsedDrawWork

/-! Every actual one-read accuracy-frame return has complete expected
common draw work at its actual retained width, using the very parsed
exponent and untouched suffix. The final parser-work attachment is free
of any additional preparation or draw execution. -/
namespace Blotto.GeneralPaperStoredFramedDrawWork
open MeasureTheory
open scoped ENNReal
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperBinaryAccuracy (Parsed)
open GeneralPaperStoredParsedPreparation (width prepare)
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192

theorem every_returned {n : ℕ} (model : RationalCostModel) (A K : ℕ) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j) (budget : ℚ) (frame : List Bool)
    (returned : GeneralPaperStoredFramedPreparation.Output)
    (hReturn : (GeneralPaperStoredFramedPreparation.run model A K values v hv budget frame).1 = some returned) :
    ∃ (parsed : Parsed) (suffix : List Bool),
      (GeneralPaperBinaryAccuracy.read id A frame).1 = some (parsed,suffix) ∧ returned.2.2 = suffix ∧
      returned.1 = width model A K values v hv budget parsed ∧
      (∫⁻ trace, ((GeneralPaperStoredSelectedLaw.observed model returned.1 returned.2.1
          (prepare model A K values v hv budget parsed).1.branch trace).work : ℝ≥0∞)
        ∂(GeneralPaperEqualBitBranchDraw.traceLaw (prepare model A K values v hv budget parsed).1.branch :
          Measure (GeneralPaperEqualBitBranchDraw.Trace (prepare model A K values v hv budget parsed).1.branch))) ≤
        (GeneralPaperStoredSelectedReturnWork.bound model returned.1 n parsed.exponent (rationalWordWidth budget) : ℝ≥0∞) := by
  obtain ⟨parsed,suffix,inner,hRead,hBuild,hEq,_⟩ := GeneralPaperStoredFramedPreparation.every_returned model A K values v hv budget frame returned hReturn
  subst returned
  refine ⟨parsed,suffix,hRead,rfl,rfl,?_⟩
  have hExpected := GeneralPaperStoredParsedDrawWork.expected_work model A K values v hv budget parsed inner hBuild
  have hExt := GeneralPaperStoredDrawWorkExt.expected_ext model
    (GeneralPaperStoredFramedPreparation.finish A (GeneralPaperBinaryAccuracy.read id A frame).2 inner suffix).1
    (GeneralPaperStoredFramedPreparation.finish A (GeneralPaperBinaryAccuracy.read id A frame).2 inner suffix).2.1 inner rfl rfl
    (prepare model A K values v hv budget parsed).1.branch
  rw [hExt]
  exact hExpected

theorem uniform_expected_work (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) (K : ℕ) :
    ∃ C d : ℕ,∀ (A n : ℕ) (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n)
      (hv : ∀ j,values.read j = v.weight j) (budget : ℚ) (frame : List Bool)
      (returned : GeneralPaperStoredFramedPreparation.Output),
      (GeneralPaperStoredFramedPreparation.run model A K values v hv budget frame).1 = some returned →
      ∃ (parsed : Parsed) (suffix : List Bool),
        (GeneralPaperBinaryAccuracy.read id A frame).1 = some (parsed,suffix) ∧ returned.2.2 = suffix ∧
        (∫⁻ trace, ((GeneralPaperStoredSelectedLaw.observed model returned.1 returned.2.1
            (prepare model A K values v hv budget parsed).1.branch trace).work : ℝ≥0∞)
          ∂(GeneralPaperEqualBitBranchDraw.traceLaw (prepare model A K values v hv budget parsed).1.branch :
            Measure (GeneralPaperEqualBitBranchDraw.Trace (prepare model A K values v hv budget parsed).1.branch))) ≤
          ((C * ((n + 1) * GeneralPaperEqualBitDrawRates.size n parsed.exponent (rationalWordWidth budget)) *
            (GeneralPaperEqualBitDrawRates.log n parsed.exponent (rationalWordWidth budget)) ^ d : ℕ) : ℝ≥0∞) := by
  obtain ⟨C,d,hC⟩ := GeneralPaperStoredPipelineDrawWork.rate model hFast 0 K
  refine ⟨C,d,?_⟩
  intro A n values v hv budget frame returned hReturn
  obtain ⟨parsed,suffix,hRead,hSuffix,hWidth,hExpected⟩ := every_returned model A K values v hv budget frame returned hReturn
  refine ⟨parsed,suffix,hRead,hSuffix,?_⟩
  have hNat : GeneralPaperStoredSelectedReturnWork.bound model returned.1 n parsed.exponent (rationalWordWidth budget) ≤
      C * ((n + 1) * GeneralPaperEqualBitDrawRates.size n parsed.exponent (rationalWordWidth budget)) *
        (GeneralPaperEqualBitDrawRates.log n parsed.exponent (rationalWordWidth budget)) ^ d := by
    rw [hWidth]
    change GeneralPaperStoredParsedDrawWork.majorant model A K values v hv budget parsed ≤ _
    rw [GeneralPaperStoredParsedDrawWork.majorant_data,
      GeneralPaperStoredPipelineDrawWork.majorant_independent model A 0 K]
    exact hC (GeneralPaperStoredParsedPreparation.input model values v hv budget parsed)
  exact hExpected.trans (by exact_mod_cast hNat)

end Blotto.GeneralPaperStoredFramedDrawWork
