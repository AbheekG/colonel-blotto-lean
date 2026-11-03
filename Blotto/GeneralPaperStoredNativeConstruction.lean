import Blotto.GeneralPaperStoredAllocationLaw

/-! Existing native retained-footprint bounds discharge actual measurement
and installation capacity. Native constructor returns and their continuous
law therefore need no caller-supplied positivity or layout-fit hypotheses. -/
namespace Blotto.GeneralPaperStoredNativeConstruction
open GeneralPaperUnifiedDirectoryInstallation (Installed)
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192

theorem address_positive {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
    (sampler : GeneralPaperEqualStoredBitSampler.Sampler G l) : 0 < sampler.address := by
  rw [sampler.address_correct]
  exact binaryWordWidth_pos _

theorem native_bounds {n : ℕ} (bits : Bool) (model : RationalCostModel) (W S k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j)
    (small : ∀ j,2 * (GeneralPaperEqualNativeSampler.rounded bits model W k values v hv).weight j ≤ 1) (budget : ℚ) :
    let sampler := GeneralPaperEqualStoredBitSampler.native bits model W k values v hv small budget
    0 < sampler.address ∧ (GeneralPaperEqualMeasuredRetainedPlan.sampler model S sampler.address sampler).sizes.sum < 2 ^ sampler.address := by
  dsimp only
  constructor
  · exact address_positive _
  · rw [GeneralPaperEqualMeasuredRetainedPlan.sampler_sum]
    exact GeneralPaperEqualNativeDrawRepresentation.native_capacity bits model W k values v hv small budget

theorem constructed {n : ℕ} (bits : Bool) (model : RationalCostModel) (W S k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j)
    (small : ∀ j,2 * (GeneralPaperEqualNativeSampler.rounded bits model W k values v hv).weight j ≤ 1) (budget : ℚ) :
    let sampler := GeneralPaperEqualStoredBitSampler.native bits model W k values v hv small budget
    ∃ returned : Installed sampler.address,
      (GeneralPaperCountedSamplerInstallation.build model S sampler).values = some returned ∧
      (GeneralPaperCountedSamplerInstallation.build model S sampler).remaining = [] ∧
      returned.work = (GeneralPaperCountedSamplerInstallation.build model S sampler).work ∧
      GeneralPaperStoredAllocationDraw.Refines model sampler.address returned sampler ∧
      GeneralPaperStoredAllocationLaw.outputLaw n model sampler.address returned sampler.prepared.D sampler.prepared.midpointBits
        (GeneralPaperEqualPreparedCache.denominator_positive sampler.prepared) = GeneralPaperEqualStoredBitSampler.outputLaw sampler model := by
  dsimp only
  let sampler := GeneralPaperEqualStoredBitSampler.native bits model W k values v hv small budget
  obtain ⟨hA,hCap⟩ := native_bounds bits model W S k values v hv small budget
  obtain ⟨returned,hReturn,hRemaining,hWork,_,_⟩ := GeneralPaperCountedSamplerInstallation.build_source model S sampler hA hCap
  exact ⟨returned,hReturn,hRemaining,hWork,
    GeneralPaperStoredAllocationDraw.every_returned model S sampler hA hCap returned hReturn,
    GeneralPaperStoredAllocationLaw.every_returned_law model S sampler hA hCap returned hReturn⟩

theorem native_epsilon {n : ℕ} (bits : Bool) (model : RationalCostModel) (W S : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j)
    (eps : ℚ) (hPositive : 0 < eps) (hOne : eps < 1)
    (small : ∀ j,2 * (GeneralPaperEqualNativeSampler.rounded bits model W
      (GeneralPaperDyadicAccuracy.prepare eps).exponent values v hv).weight j ≤ 1) (budget : ℚ) (hBudget : 0 < budget) :
    let sampler := GeneralPaperEqualStoredBitSampler.native bits model W (GeneralPaperDyadicAccuracy.prepare eps).exponent values v hv small budget
    ∃ returned : Installed sampler.address,
      (GeneralPaperCountedSamplerInstallation.build model S sampler).values = some returned ∧
      (GeneralPaperCountedSamplerInstallation.build model S sampler).remaining = [] ∧
      returned.work = (GeneralPaperCountedSamplerInstallation.build model S sampler).work ∧
      let μ := GeneralPaperStoredAllocationLaw.outputLaw n model sampler.address returned sampler.prepared.D sampler.prepared.midpointBits
        (GeneralPaperEqualPreparedCache.denominator_positive sampler.prepared)
      Supported (budget : ℝ) μ ∧ regret v.values (budget : ℝ) μ μ ≤ (eps : ℝ) := by
  dsimp only
  obtain ⟨returned,hReturn,hRemaining,hWork,_,hLaw⟩ := constructed bits model W S (GeneralPaperDyadicAccuracy.prepare eps).exponent values v hv small budget
  refine ⟨returned,hReturn,hRemaining,hWork,?_⟩
  rw [hLaw]
  exact GeneralPaperEqualStoredBitSampler.native_epsilon bits model W values v hv eps hPositive hOne small budget hBudget

end Blotto.GeneralPaperStoredNativeConstruction
