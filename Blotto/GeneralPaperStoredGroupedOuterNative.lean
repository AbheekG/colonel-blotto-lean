import Blotto.GeneralPaperStoredGroupedOuterConstruction

/-! Native grouped construction derives both pool capacities from the
existing inner/selected retained bounds. No supplied storage-fit hypotheses
are needed to construct an actual mixed-width return with draw refinement. -/
namespace Blotto.GeneralPaperStoredGroupedOuterNative
open GeneralPaperUnifiedDirectoryInstallation (Installed)
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192

theorem bounds {n : ℕ} (model : RationalCostModel) (W S k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j)
    (small : ∀ j,2 * (GeneralPaperEqualNativeSampler.rounded true model W k values v hv).weight j ≤ 1) (budget : ℚ) :
    let sampler := GeneralPaperEqualStoredBitSampler.native true model W k values v hv small budget
    (GeneralPaperEqualMeasuredRetainedPlan.sampler model S sampler.address sampler).sizes.sum < 2 ^ sampler.address ∧
      (GeneralPaperEqualMeasuredRetainedPlan.sampler model S sampler.address sampler).sizes.sum +
      (GeneralPaperEqualMeasuredSelectedPlan.header model S (sampler.address + 1)).sizes.sum < 2 ^ (sampler.address + 1) := by
  dsimp only
  let sampler := GeneralPaperEqualStoredBitSampler.native true model W k values v hv small budget
  refine ⟨(GeneralPaperStoredNativeConstruction.native_bounds true model W S k values v hv small budget).2,?_⟩
  let selected : GeneralPaperEqualSelectedSampler.Sampler (GeneralPaperEqualNativeSampler.rounded true model W k values v hv) k budget :=
    ⟨.grouped small sampler rfl rfl,sampler.address + 1,rfl⟩
  rw [GeneralPaperEqualMeasuredRetainedPlan.sampler_sum,GeneralPaperEqualMeasuredSelectedPlan.header_sum]
  exact GeneralPaperEqualSelectedDescription.capacity model W k values v hv budget selected

theorem constructed {n : ℕ} (model : RationalCostModel) (W S k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j)
    (small : ∀ j,2 * (GeneralPaperEqualNativeSampler.rounded true model W k values v hv).weight j ≤ 1) (budget : ℚ) :
    let sampler := GeneralPaperEqualStoredBitSampler.native true model W k values v hv small budget
    ∃ returned : Installed (sampler.address + 1),
      (GeneralPaperStoredGroupedOuterConstruction.run model S sampler).values = some returned ∧
      (GeneralPaperStoredGroupedOuterConstruction.run model S sampler).remaining = [] ∧
      returned.work = (GeneralPaperStoredGroupedOuterConstruction.run model S sampler).work ∧
      GeneralPaperStoredGroupedOuterDraw.Refines model (sampler.address + 1) returned sampler := by
  obtain ⟨hInner,hOuter⟩ := bounds model W S k values v hv small budget
  exact GeneralPaperStoredGroupedOuterConstruction.source model S _ hInner hOuter

end Blotto.GeneralPaperStoredGroupedOuterNative
