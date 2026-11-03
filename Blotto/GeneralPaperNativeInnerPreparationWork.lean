import Blotto.GeneralPaperCompleteInnerPreparationWork

/-! Native actual one-memory construction costs derive their address/capacity
conditions internally and join the very same returned runtime and canonical
law. Retained-cache creation is charged by its existing source pipeline;
these bounds cover the complete subsequent measured one-memory constructor. -/
namespace Blotto.GeneralPaperNativeInnerPreparationWork
open GeneralPaperUnifiedDirectoryInstallation (Installed)
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192

theorem build_work {n : ℕ} (bits : Bool) (model : RationalCostModel) (W S k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j)
    (small : ∀ j,2 * (GeneralPaperEqualNativeSampler.rounded bits model W k values v hv).weight j ≤ 1) (budget : ℚ) :
    let source := GeneralPaperEqualStoredBitSampler.native bits model W k values v hv small budget
    (GeneralPaperCountedSamplerInstallation.build model S source).work ≤
      GeneralPaperCompleteInnerPreparationWork.bound model S source.address
        (GeneralPaperEqualMeasuredRetainedPlan.sampler model S source.address source).sizes.sum := by
  dsimp only
  obtain ⟨hA,hCap⟩ := GeneralPaperStoredNativeConstruction.native_bounds bits model W S k values v hv small budget
  exact GeneralPaperCompleteInnerPreparationWork.build_work model S _ hA hCap

theorem every_returned {n : ℕ} (bits : Bool) (model : RationalCostModel) (W S k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j)
    (small : ∀ j,2 * (GeneralPaperEqualNativeSampler.rounded bits model W k values v hv).weight j ≤ 1) (budget : ℚ)
    (returned : Installed (GeneralPaperEqualStoredBitSampler.native bits model W k values v hv small budget).address)
    (hReturn : (GeneralPaperCountedSamplerInstallation.build model S
      (GeneralPaperEqualStoredBitSampler.native bits model W k values v hv small budget)).values = some returned) :
    let source := GeneralPaperEqualStoredBitSampler.native bits model W k values v hv small budget
    returned.work ≤ GeneralPaperCompleteInnerPreparationWork.bound model S source.address
      (GeneralPaperEqualMeasuredRetainedPlan.sampler model S source.address source).sizes.sum := by
  dsimp only
  obtain ⟨hA,hCap⟩ := GeneralPaperStoredNativeConstruction.native_bounds bits model W S k values v hv small budget
  exact GeneralPaperCompleteInnerPreparationWork.every_returned_work model S _ hA hCap returned hReturn

theorem constructed {n : ℕ} (bits : Bool) (model : RationalCostModel) (W S k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j)
    (small : ∀ j,2 * (GeneralPaperEqualNativeSampler.rounded bits model W k values v hv).weight j ≤ 1) (budget : ℚ) :
    let source := GeneralPaperEqualStoredBitSampler.native bits model W k values v hv small budget
    ∃ returned : Installed source.address,
      (GeneralPaperCountedSamplerInstallation.build model S source).values = some returned ∧
      (GeneralPaperCountedSamplerInstallation.build model S source).remaining = [] ∧
      returned.work = (GeneralPaperCountedSamplerInstallation.build model S source).work ∧
      returned.work ≤ GeneralPaperCompleteInnerPreparationWork.bound model S source.address
        (GeneralPaperEqualMeasuredRetainedPlan.sampler model S source.address source).sizes.sum ∧
      GeneralPaperStoredAllocationDraw.Refines model source.address returned source ∧
      GeneralPaperStoredAllocationLaw.outputLaw n model source.address returned source.prepared.D source.prepared.midpointBits
        (GeneralPaperEqualPreparedCache.denominator_positive source.prepared) = GeneralPaperEqualStoredBitSampler.outputLaw source model := by
  dsimp only
  obtain ⟨returned,hReturn,hRest,hWork,hRefines,hLaw⟩ := GeneralPaperStoredNativeConstruction.constructed bits model W S k values v hv small budget
  exact ⟨returned,hReturn,hRest,hWork,every_returned bits model W S k values v hv small budget returned hReturn,hRefines,hLaw⟩

theorem native_epsilon {n : ℕ} (bits : Bool) (model : RationalCostModel) (W S : ℕ)
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
      let μ := GeneralPaperStoredAllocationLaw.outputLaw n model source.address returned source.prepared.D source.prepared.midpointBits
        (GeneralPaperEqualPreparedCache.denominator_positive source.prepared)
      Supported (budget : ℝ) μ ∧ regret v.values (budget : ℝ) μ μ ≤ (eps : ℝ) := by
  dsimp only
  obtain ⟨returned,hReturn,hRest,hWork,hLaw⟩ := GeneralPaperStoredNativeConstruction.native_epsilon bits model W S values v hv eps hPositive hOne small budget hBudget
  exact ⟨returned,hReturn,hRest,hWork,every_returned bits model W S (GeneralPaperDyadicAccuracy.prepare eps).exponent
    values v hv small budget returned hReturn,hLaw⟩

end Blotto.GeneralPaperNativeInnerPreparationWork
