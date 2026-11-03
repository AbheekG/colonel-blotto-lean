import Blotto.GeneralPaperSelectedCursorLifetime

/-! Native grouped cursor lifetimes in both bits modes. Existing native
source contracts derive all width/capacity premises; the actual installed
return joins full work, runtime refinement/canonical law and cursor storage. -/
namespace Blotto.GeneralPaperNativeCursorLifetime
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperRulerCursorLifetime (encoding)
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192

theorem grouped_cursor {n : ℕ} (bits : Bool) (model : RationalCostModel) (W S k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j)
    (small : ∀ j,2 * (GeneralPaperEqualNativeSampler.rounded bits model W k values v hv).weight j ≤ 1) (budget : ℚ) :
    let source := GeneralPaperEqualStoredBitSampler.native bits model W k values v hv small budget
    GeneralPaperSamplerCursorLifetime.window model S source.address 0 source [] ≤
      GeneralPaperRecordCursorLifetimeRates.profile model S source.address
        (GeneralPaperEqualMeasuredRetainedPlan.sampler model S source.address source).sizes.sum 168 (496 + encoding model S source.address) := by
  dsimp only
  obtain ⟨hA,hCap⟩ := GeneralPaperStoredNativeConstruction.native_bounds bits model W S k values v hv small budget
  exact GeneralPaperSamplerCursorLifetime.actual model S _ 0 _ [] hA (by simpa only [Nat.zero_add] using hCap)

theorem grouped_constructed {n : ℕ} (bits : Bool) (model : RationalCostModel) (W S k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j)
    (small : ∀ j,2 * (GeneralPaperEqualNativeSampler.rounded bits model W k values v hv).weight j ≤ 1) (budget : ℚ) :
    let source := GeneralPaperEqualStoredBitSampler.native bits model W k values v hv small budget
    ∃ returned : Installed source.address,
      (GeneralPaperCountedSamplerInstallation.build model S source).values = some returned ∧
      (GeneralPaperCountedSamplerInstallation.build model S source).remaining = [] ∧
      returned.work = (GeneralPaperCountedSamplerInstallation.build model S source).work ∧
      returned.work ≤ GeneralPaperCompleteInnerPreparationWork.bound model S source.address
        (GeneralPaperEqualMeasuredRetainedPlan.sampler model S source.address source).sizes.sum ∧
      GeneralPaperSamplerCursorLifetime.window model S source.address 0 source [] ≤
        GeneralPaperRecordCursorLifetimeRates.profile model S source.address
          (GeneralPaperEqualMeasuredRetainedPlan.sampler model S source.address source).sizes.sum 168 (496 + encoding model S source.address) ∧
      GeneralPaperStoredAllocationDraw.Refines model source.address returned source ∧
      GeneralPaperStoredAllocationLaw.outputLaw n model source.address returned source.prepared.D source.prepared.midpointBits
        (GeneralPaperEqualPreparedCache.denominator_positive source.prepared) = GeneralPaperEqualStoredBitSampler.outputLaw source model := by
  dsimp only
  obtain ⟨returned,hReturn,hRest,hWork,hCost,hRefines,hLaw⟩ :=
    GeneralPaperNativeInnerPreparationWork.constructed bits model W S k values v hv small budget
  exact ⟨returned,hReturn,hRest,hWork,hCost,grouped_cursor bits model W S k values v hv small budget,hRefines,hLaw⟩

theorem grouped_epsilon {n : ℕ} (bits : Bool) (model : RationalCostModel) (W S : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j)
    (eps : ℚ) (hPositive : 0 < eps) (hOne : eps < 1)
    (small : ∀ j,2 * (GeneralPaperEqualNativeSampler.rounded bits model W
      (GeneralPaperDyadicAccuracy.prepare eps).exponent values v hv).weight j ≤ 1) (budget : ℚ) (hBudget : 0 < budget) :
    let source := GeneralPaperEqualStoredBitSampler.native bits model W (GeneralPaperDyadicAccuracy.prepare eps).exponent values v hv small budget
    ∃ returned : Installed source.address,
      (GeneralPaperCountedSamplerInstallation.build model S source).values = some returned ∧
      (GeneralPaperCountedSamplerInstallation.build model S source).remaining = [] ∧
      returned.work = (GeneralPaperCountedSamplerInstallation.build model S source).work ∧
      returned.work ≤ GeneralPaperCompleteInnerPreparationWork.bound model S source.address
        (GeneralPaperEqualMeasuredRetainedPlan.sampler model S source.address source).sizes.sum ∧
      GeneralPaperSamplerCursorLifetime.window model S source.address 0 source [] ≤
        GeneralPaperRecordCursorLifetimeRates.profile model S source.address
          (GeneralPaperEqualMeasuredRetainedPlan.sampler model S source.address source).sizes.sum 168 (496 + encoding model S source.address) ∧
      let μ := GeneralPaperStoredAllocationLaw.outputLaw n model source.address returned source.prepared.D source.prepared.midpointBits
        (GeneralPaperEqualPreparedCache.denominator_positive source.prepared)
      Supported (budget : ℝ) μ ∧ regret v.values (budget : ℝ) μ μ ≤ (eps : ℝ) := by
  dsimp only
  obtain ⟨returned,hReturn,hRest,hWork,hCost,hLaw⟩ :=
    GeneralPaperNativeInnerPreparationWork.native_epsilon bits model W S values v hv eps hPositive hOne small budget hBudget
  exact ⟨returned,hReturn,hRest,hWork,hCost,
    grouped_cursor bits model W S (GeneralPaperDyadicAccuracy.prepare eps).exponent values v hv small budget,hLaw⟩

end Blotto.GeneralPaperNativeCursorLifetime
