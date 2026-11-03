import Blotto.GeneralPaperTwoPoolPreparationWork

/-! Complete actual grouped and dominant outer preparation. The parent pays
one two-pool layout and consumes the already-priced inner prefix return.
Outer fields then extend that returned memory exactly once. -/
namespace Blotto.GeneralPaperCompleteOuterPreparationWork
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperEqualOuterFieldLayout
open GeneralPaperMeasuredPlanWorkAlgebra
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192

def groupedBound {n m q : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m q}
    (model : RationalCostModel) (S : ℕ) (source : GeneralPaperEqualStoredBitSampler.Sampler G l) : ℕ :=
  GeneralPaperTwoPoolPreparationWork.bound model S source.address (source.address + 1)
    (GeneralPaperEqualMeasuredRetainedPlan.sampler model S source.address source).sizes.sum
    (GeneralPaperEqualMeasuredSelectedPlan.header model S (source.address + 1)).sizes.sum

theorem grouped_work {n m q : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m q}
    (model : RationalCostModel) (S : ℕ) (source : GeneralPaperEqualStoredBitSampler.Sampler G l)
    (hInnerCap : (GeneralPaperEqualMeasuredRetainedPlan.sampler model S source.address source).sizes.sum < 2 ^ source.address)
    (hOuterCap : (GeneralPaperEqualMeasuredRetainedPlan.sampler model S source.address source).sizes.sum +
      (GeneralPaperEqualMeasuredSelectedPlan.header model S (source.address + 1)).sizes.sum < 2 ^ (source.address + 1)) :
    (GeneralPaperStoredGroupedOuterConstruction.run model S source).work ≤ groupedBound model S source := by
  have hI := GeneralPaperStoredNativeConstruction.address_positive source
  have hA : 0 < source.address + 1 := by omega
  have hLayout := GeneralPaperTwoPoolPreparationWork.layout_work model S source.address (source.address + 1)
    (GeneralPaperEqualMeasuredRetainedPlan.sampler model S source.address source)
    (GeneralPaperMeasuredRetainedPlanWork.sampler model S source.address source hI) hI hA hInnerCap hOuterCap
  obtain ⟨inner,hInner,_,_,_,_⟩ := GeneralPaperCountedSamplerInstallation.sampler_prefix model S source.address 0 source [] hI
    (by simpa only [Nat.zero_add] using hInnerCap)
  simp only [List.append_nil] at hInner
  have hInnerActual : (GeneralPaperCountedSamplerInstallation.run model S source.address source
      (GeneralPaperStoredGroupedOuterConstruction.layout model S source).inner).values = some inner := hInner
  have hInnerWork := GeneralPaperCompleteInnerPreparationWork.every_sampler_prefix_returned model S source.address 0 source [] hI
    (by simpa only [Nat.zero_add] using hInnerCap) inner (by simpa only [List.append_nil] using hInner)
  have hBoundary : (GeneralPaperStoredGroupedOuterConstruction.layout model S source).boundary =
      (GeneralPaperEqualMeasuredRetainedPlan.sampler model S source.address source).sizes.sum :=
    GeneralPaperMeasuredTwoPoolLayout.boundary model S source.address (source.address + 1) _ _
  have hOuterStartCap : (GeneralPaperStoredGroupedOuterConstruction.layout model S source).boundary +
      (GeneralPaperEqualMeasuredSelectedPlan.header model S (source.address + 1)).sizes.sum < 2 ^ (source.address + 1) := by
    rw [hBoundary]; exact hOuterCap
  have hFields := GeneralPaperTwoPoolPreparationWork.extract_work model S (source.address + 1)
    (GeneralPaperStoredGroupedOuterConstruction.layout model S source).boundary hA hOuterStartCap
  change (extract S (source.address + 1) (GeneralPaperStoredGroupedOuterConstruction.layout model S source).outer).2 ≤ _ at hFields
  have hTag : 1 < 2 ^ (source.address + 1) := by
    have h : 0 < 2 ^ source.address := by positivity
    rw [pow_succ]
    omega
  have hOuter := GeneralPaperStoredPreparationConstructorWork.outer_work model S source.address (source.address + 1)
    (GeneralPaperStoredGroupedOuterConstruction.layout model S source).boundary
    ((GeneralPaperStoredGroupedOuterConstruction.layout model S source).work +
      (extract S (source.address + 1) (GeneralPaperStoredGroupedOuterConstruction.layout model S source).outer).2)
    1 inner hA (Nat.le_succ _) hTag hOuterStartCap
  change (GeneralPaperStoredGroupedOuterConstruction.layout model S source).work ≤ _ at hLayout
  simp only [GeneralPaperStoredGroupedOuterConstruction.run,hInnerActual,GeneralPaperStoredGroupedOuterConstruction.fields_source]
  unfold groupedBound GeneralPaperTwoPoolPreparationWork.bound
  nlinarith only [hLayout,hInnerWork,hFields,hOuter]

theorem grouped_returned {n m q : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m q}
    (model : RationalCostModel) (S : ℕ) (source : GeneralPaperEqualStoredBitSampler.Sampler G l)
    (hInnerCap : (GeneralPaperEqualMeasuredRetainedPlan.sampler model S source.address source).sizes.sum < 2 ^ source.address)
    (hOuterCap : (GeneralPaperEqualMeasuredRetainedPlan.sampler model S source.address source).sizes.sum +
      (GeneralPaperEqualMeasuredSelectedPlan.header model S (source.address + 1)).sizes.sum < 2 ^ (source.address + 1))
    (returned : Installed (source.address + 1)) (hReturn : (GeneralPaperStoredGroupedOuterConstruction.run model S source).values = some returned) :
    returned.work ≤ groupedBound model S source := by
  obtain ⟨actual,hActual,_,hWork,_⟩ := GeneralPaperStoredGroupedOuterConstruction.source model S source hInnerCap hOuterCap
  have hSame : actual = returned := Option.some.inj (hActual.symm.trans hReturn)
  rw [← hSame,hWork]
  exact grouped_work model S source hInnerCap hOuterCap

def dominantBound {n : ℕ} (model : RationalCostModel) (S A chosen : ℕ) (source : RationalResourceArray n) : ℕ :=
  GeneralPaperTwoPoolPreparationWork.bound model S A A (GeneralPaperStoredDominantCursor.plan model S A chosen source).sizes.sum
    (GeneralPaperEqualMeasuredSelectedPlan.header model S A).sizes.sum

theorem dominant_work {n : ℕ} (model : RationalCostModel) (S A chosen : ℕ) (source : RationalResourceArray n)
    (hA : 0 < A) (hInnerCap : (GeneralPaperStoredDominantCursor.plan model S A chosen source).sizes.sum < 2 ^ A)
    (hOuterCap : (GeneralPaperStoredDominantCursor.plan model S A chosen source).sizes.sum +
      (GeneralPaperEqualMeasuredSelectedPlan.header model S A).sizes.sum < 2 ^ A) :
    (GeneralPaperStoredDominantOuterConstruction.run model S A chosen source).work ≤ dominantBound model S A chosen source := by
  have hPlan := mono model S A 34 1909 _ (GeneralPaperTwoPoolPreparationWork.dominant_plan model S A chosen source hA) (by decide)
  have hLayout := GeneralPaperTwoPoolPreparationWork.layout_work model S A A
    (GeneralPaperStoredDominantCursor.plan model S A chosen source) hPlan hA hA hInnerCap hOuterCap
  obtain ⟨inner,hInner,_,_,_,_⟩ := GeneralPaperStoredDominantInstallation.source model S A 0 chosen source [] hA
    (by simpa only [Nat.zero_add] using hInnerCap)
  simp only [List.append_nil] at hInner
  have hInnerActual : (GeneralPaperStoredDominantInstallation.run model S A chosen source
      (GeneralPaperStoredDominantOuterConstruction.layout model S A chosen source).inner).values = some inner := hInner
  have hInnerWork := GeneralPaperCompleteInnerPreparationWork.every_dominant_prefix_returned model S A 0 chosen source [] hA
    (by simpa only [Nat.zero_add] using hInnerCap) inner (by simpa only [List.append_nil] using hInner)
  have hUp := Nat.mul_le_mul_right (unit model S A)
    (Nat.mul_le_mul_left ((GeneralPaperStoredDominantCursor.plan model S A chosen source).sizes.sum + 1) (show 48 ≤ 168 by decide))
  have hBoundary : (GeneralPaperStoredDominantOuterConstruction.layout model S A chosen source).boundary =
      (GeneralPaperStoredDominantCursor.plan model S A chosen source).sizes.sum :=
    GeneralPaperMeasuredTwoPoolLayout.boundary model S A A _ _
  have hOuterStartCap : (GeneralPaperStoredDominantOuterConstruction.layout model S A chosen source).boundary +
      (GeneralPaperEqualMeasuredSelectedPlan.header model S A).sizes.sum < 2 ^ A := by rw [hBoundary]; exact hOuterCap
  have hFields := GeneralPaperTwoPoolPreparationWork.extract_work model S A
    (GeneralPaperStoredDominantOuterConstruction.layout model S A chosen source).boundary hA hOuterStartCap
  change (extract S A (GeneralPaperStoredDominantOuterConstruction.layout model S A chosen source).outer).2 ≤ _ at hFields
  have hOuter := GeneralPaperStoredPreparationConstructorWork.outer_work model S A A
    (GeneralPaperStoredDominantOuterConstruction.layout model S A chosen source).boundary
    ((GeneralPaperStoredDominantOuterConstruction.layout model S A chosen source).work +
      (extract S A (GeneralPaperStoredDominantOuterConstruction.layout model S A chosen source).outer).2)
    0 inner hA le_rfl (by positivity) hOuterStartCap
  change (GeneralPaperStoredDominantOuterConstruction.layout model S A chosen source).work ≤ _ at hLayout
  simp only [GeneralPaperStoredDominantOuterConstruction.run,hInnerActual,GeneralPaperStoredDominantOuterConstruction.fields_source]
  unfold dominantBound GeneralPaperTwoPoolPreparationWork.bound
  nlinarith only [hLayout,hInnerWork,hUp,hFields,hOuter]

theorem dominant_returned {n : ℕ} (model : RationalCostModel) (S A chosen : ℕ) (source : RationalResourceArray n)
    (hA : 0 < A) (hInnerCap : (GeneralPaperStoredDominantCursor.plan model S A chosen source).sizes.sum < 2 ^ A)
    (hOuterCap : (GeneralPaperStoredDominantCursor.plan model S A chosen source).sizes.sum +
      (GeneralPaperEqualMeasuredSelectedPlan.header model S A).sizes.sum < 2 ^ A)
    (returned : Installed A) (hReturn : (GeneralPaperStoredDominantOuterConstruction.run model S A chosen source).values = some returned) :
    returned.work ≤ dominantBound model S A chosen source := by
  obtain ⟨actual,hActual,_,hWork,_⟩ := GeneralPaperStoredDominantOuterConstruction.source model S A chosen source hA hInnerCap hOuterCap
  have hSame : actual = returned := Option.some.inj (hActual.symm.trans hReturn)
  rw [← hSame,hWork]
  exact dominant_work model S A chosen source hA hInnerCap hOuterCap

end Blotto.GeneralPaperCompleteOuterPreparationWork
