import Blotto.GeneralPaperStoredDominantOuterWork

/-! Every actual outer constructor return has the bounded marker read
used by common dispatch. This follows from its actual outer writes and
measured owner, independently of the inner draw's random outcome. -/
namespace Blotto.GeneralPaperStoredReturnedMarkerWork
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperEqualOuterFieldLayout
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192

theorem grouped {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
    (model : RationalCostModel) (S : ℕ) (sampler : GeneralPaperEqualStoredBitSampler.Sampler G l)
    (hCap : (GeneralPaperEqualMeasuredRetainedPlan.sampler model S sampler.address sampler).sizes.sum +
      (GeneralPaperEqualMeasuredSelectedPlan.header model S (sampler.address + 1)).sizes.sum < 2 ^ (sampler.address + 1))
    (returned : Installed (sampler.address + 1))
    (hReturn : (GeneralPaperStoredGroupedOuterConstruction.run model S sampler).values = some returned) :
    (GeneralPaperStoredOuterMarker.read model (sampler.address + 1) returned).2 ≤
      GeneralPaperStoredOuterReadWork.markerBound model (sampler.address + 1) := by
  simp only [GeneralPaperStoredGroupedOuterConstruction.run,GeneralPaperStoredGroupedOuterConstruction.fields_source] at hReturn
  cases hInner : (GeneralPaperCountedSamplerInstallation.run model S sampler.address sampler
      (GeneralPaperStoredGroupedOuterConstruction.layout model S sampler).inner).values with
  | none => simp only [hInner] at hReturn; cases hReturn
  | some inner =>
    simp only [hInner] at hReturn
    rw [← Option.some.inj hReturn]
    have hCapActual : (GeneralPaperStoredGroupedOuterConstruction.layout model S sampler).boundary +
        (GeneralPaperEqualMeasuredSelectedPlan.header model S (sampler.address + 1)).sizes.sum < 2 ^ (sampler.address + 1) := by
      simpa only [GeneralPaperStoredGroupedOuterConstruction.layout,GeneralPaperMeasuredTwoPoolLayout.boundary] using hCap
    have hRead := GeneralPaperStoredOuterAttachment.outer_readback model S sampler.address (sampler.address + 1)
      (GeneralPaperStoredGroupedOuterConstruction.layout model S sampler).boundary
      ((GeneralPaperStoredGroupedOuterConstruction.layout model S sampler).work +
        (extract S (sampler.address + 1) (GeneralPaperStoredGroupedOuterConstruction.layout model S sampler).outer).2) inner 1 (by omega) hCapActual
    have hCapacity := GeneralPaperStoredOuterReadWork.capacity model S (sampler.address + 1)
      (GeneralPaperStoredGroupedOuterConstruction.layout model S sampler).boundary (by omega) hCapActual
    exact GeneralPaperStoredOuterReadWork.marker_work model (sampler.address + 1) 1 _ _ _ hRead rfl hCapacity.1 (by omega)

theorem dominant {n : ℕ} (model : RationalCostModel) (S A chosen : ℕ) (row : RationalResourceArray n)
    (hA : 0 < A) (hCap : (GeneralPaperStoredDominantCursor.plan model S A chosen row).sizes.sum +
      (GeneralPaperEqualMeasuredSelectedPlan.header model S A).sizes.sum < 2 ^ A)
    (returned : Installed A) (hReturn : (GeneralPaperStoredDominantOuterConstruction.run model S A chosen row).values = some returned) :
    (GeneralPaperStoredOuterMarker.read model A returned).2 ≤ GeneralPaperStoredOuterReadWork.markerBound model A := by
  simp only [GeneralPaperStoredDominantOuterConstruction.run,GeneralPaperStoredDominantOuterConstruction.fields_source] at hReturn
  cases hInner : (GeneralPaperStoredDominantInstallation.run model S A chosen row
      (GeneralPaperStoredDominantOuterConstruction.layout model S A chosen row).inner).values with
  | none => simp only [hInner] at hReturn; cases hReturn
  | some inner =>
    simp only [hInner] at hReturn
    rw [← Option.some.inj hReturn]
    have hCapActual : (GeneralPaperStoredDominantOuterConstruction.layout model S A chosen row).boundary +
        (GeneralPaperEqualMeasuredSelectedPlan.header model S A).sizes.sum < 2 ^ A := by
      simpa only [GeneralPaperStoredDominantOuterConstruction.layout,GeneralPaperMeasuredTwoPoolLayout.boundary] using hCap
    have hRead := GeneralPaperStoredOuterAttachment.outer_readback model S A A
      (GeneralPaperStoredDominantOuterConstruction.layout model S A chosen row).boundary
      ((GeneralPaperStoredDominantOuterConstruction.layout model S A chosen row).work +
        (extract S A (GeneralPaperStoredDominantOuterConstruction.layout model S A chosen row).outer).2) inner 0 hA hCapActual
    have hCapacity := GeneralPaperStoredOuterReadWork.capacity model S A
      (GeneralPaperStoredDominantOuterConstruction.layout model S A chosen row).boundary hA hCapActual
    exact GeneralPaperStoredOuterReadWork.marker_work model A 0 _ _ _ hRead rfl hCapacity.1 (by omega)

end Blotto.GeneralPaperStoredReturnedMarkerWork
