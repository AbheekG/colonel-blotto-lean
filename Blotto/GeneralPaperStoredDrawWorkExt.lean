import Blotto.GeneralPaperStoredSelectedReturnWork

/-! Equal installed memory/root preserves the complete common observation
and expected work. Preparation-work attachments therefore do not rerun
preparation or alter the draw price. -/
namespace Blotto.GeneralPaperStoredDrawWorkExt
open MeasureTheory
open scoped ENNReal
open GeneralPaperUnifiedDirectoryInstallation (Installed)
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192

theorem observed_ext {n : ℕ} (model : RationalCostModel) (A : ℕ) (first second : Installed A)
    (hMemory : first.memory = second.memory) (hRoot : first.root = second.root)
    {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ} (p : GeneralPaperEqualBitBranch.Prepared v k budget)
    (trace : GeneralPaperEqualBitBranchDraw.Trace p) :
    GeneralPaperStoredSelectedLaw.observed model A first p trace = GeneralPaperStoredSelectedLaw.observed model A second p trace := by
  cases p with
  | dominant chosen heavy row correct =>
    exact GeneralPaperStoredSelectedExt.run_ext model A first second hMemory hRoot 0 (fun _ => []) GeneralPaperBooleanFreshWord.nextList []
  | grouped small sampler hK hB =>
    exact GeneralPaperStoredSelectedExt.run_ext model A first second hMemory hRoot (trace.1 + 1) _ GeneralPaperBooleanFreshWord.nextList _

theorem expected_ext {n : ℕ} (model : RationalCostModel) (A : ℕ) (first second : Installed A)
    (hMemory : first.memory = second.memory) (hRoot : first.root = second.root)
    {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ} (p : GeneralPaperEqualBitBranch.Prepared v k budget) :
    (∫⁻ trace, ((GeneralPaperStoredSelectedLaw.observed model A first p trace).work : ℝ≥0∞)
      ∂(GeneralPaperEqualBitBranchDraw.traceLaw p : Measure (GeneralPaperEqualBitBranchDraw.Trace p))) =
    (∫⁻ trace, ((GeneralPaperStoredSelectedLaw.observed model A second p trace).work : ℝ≥0∞)
      ∂(GeneralPaperEqualBitBranchDraw.traceLaw p : Measure (GeneralPaperEqualBitBranchDraw.Trace p))) := by
  apply lintegral_congr_ae
  filter_upwards [] with trace
  rw [observed_ext model A first second hMemory hRoot p trace]

end Blotto.GeneralPaperStoredDrawWorkExt
