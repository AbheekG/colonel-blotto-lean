import Blotto.GeneralPaperCompleteSamplerCursorWork

/-! Complete actual inner preparation prices with no unproved cursor cost.
Measured-plan work, layout, extraction, count initialization and one unified
installation are joined for grouped builds. Both grouped and dominant prefix
constructors have complete prices; enclosing two-pool work stays separate. -/
namespace Blotto.GeneralPaperCompleteInnerPreparationWork
open GeneralPaperSequentialLayout GeneralPaperMeasuredPlanWorkAlgebra
open GeneralPaperUniformResourceGrowth GeneralPaperEqualUniformRateAlgebra
open GeneralPaperUnifiedDirectoryInstallation (Installed)
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192

def bound (model : RationalCostModel) (S A B : ℕ) : ℕ :=
  (B + 1) * 2077 * unit model S A + (B + 1) * GeneralPaperSequentialLayout.stepPrice model S A +
    GeneralPaperStoredDirectoryPreparationWork.bound model S A B + 128 * (S + A + 1)

theorem sampler_prefix_work {n m q : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m q}
    (model : RationalCostModel) (S A start : ℕ) (source : GeneralPaperEqualStoredBitSampler.Sampler G l)
    (rest : List (Region A)) (hA : 0 < A)
    (hCap : start + (GeneralPaperEqualMeasuredRetainedPlan.sampler model S A source).sizes.sum < 2 ^ A) :
    (GeneralPaperCountedSamplerInstallation.run model S A source
      ((GeneralPaperMeasuredBlockLayout.run model S A start (GeneralPaperEqualMeasuredRetainedPlan.sampler model S A source)).1 ++ rest)).work ≤
      ((GeneralPaperEqualMeasuredRetainedPlan.sampler model S A source).sizes.sum + 1) * 168 * unit model S A +
        GeneralPaperStoredDirectoryPreparationWork.bound model S A (GeneralPaperEqualMeasuredRetainedPlan.sampler model S A source).sizes.sum := by
  have hCursor := GeneralPaperCompleteSamplerCursorWork.sampler model S A start source rest hA hCap
  have hInstall := GeneralPaperStoredPreparationConstructorWork.sampler_prefix_work model S A start source rest hA hCap
  dsimp only at hInstall
  omega

theorem every_sampler_prefix_returned {n m q : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m q}
    (model : RationalCostModel) (S A start : ℕ) (source : GeneralPaperEqualStoredBitSampler.Sampler G l)
    (rest : List (Region A)) (hA : 0 < A)
    (hCap : start + (GeneralPaperEqualMeasuredRetainedPlan.sampler model S A source).sizes.sum < 2 ^ A)
    (returned : Installed A)
    (hReturn : (GeneralPaperCountedSamplerInstallation.run model S A source
      ((GeneralPaperMeasuredBlockLayout.run model S A start (GeneralPaperEqualMeasuredRetainedPlan.sampler model S A source)).1 ++ rest)).values = some returned) :
    returned.work ≤ ((GeneralPaperEqualMeasuredRetainedPlan.sampler model S A source).sizes.sum + 1) * 168 * unit model S A +
      GeneralPaperStoredDirectoryPreparationWork.bound model S A (GeneralPaperEqualMeasuredRetainedPlan.sampler model S A source).sizes.sum := by
  obtain ⟨actual,hActual,_,hWork,_,_⟩ := GeneralPaperCountedSamplerInstallation.sampler_prefix model S A start source rest hA hCap
  have hSame : actual = returned := Option.some.inj (hActual.symm.trans hReturn)
  rw [← hSame,hWork]
  exact sampler_prefix_work model S A start source rest hA hCap

theorem constructor_majorant {n m q : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m q}
    (model : RationalCostModel) (S : ℕ) (source : GeneralPaperEqualStoredBitSampler.Sampler G l)
    (hA : 0 < source.address)
    (hCap : (GeneralPaperEqualMeasuredRetainedPlan.sampler model S source.address source).sizes.sum < 2 ^ source.address) :
    GeneralPaperMeasuredPlanWorkRates.constructorBound model S source.address
      (GeneralPaperEqualMeasuredRetainedPlan.sampler model S source.address source).sizes.sum
      (GeneralPaperSamplerRecordCursor.run model S source.address source
        (GeneralPaperMeasuredBlockLayout.run model S source.address 0 (GeneralPaperEqualMeasuredRetainedPlan.sampler model S source.address source)).1).work ≤
      bound model S source.address (GeneralPaperEqualMeasuredRetainedPlan.sampler model S source.address source).sizes.sum := by
  have hCursor := GeneralPaperCompleteSamplerCursorWork.sampler model S source.address 0 source [] hA
    (by simpa only [Nat.zero_add] using hCap)
  simp only [List.append_nil] at hCursor
  unfold GeneralPaperMeasuredPlanWorkRates.constructorBound bound
  nlinarith only [hCursor]

theorem build_work {n m q : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m q}
    (model : RationalCostModel) (S : ℕ) (source : GeneralPaperEqualStoredBitSampler.Sampler G l)
    (hA : 0 < source.address)
    (hCap : (GeneralPaperEqualMeasuredRetainedPlan.sampler model S source.address source).sizes.sum < 2 ^ source.address) :
    (GeneralPaperCountedSamplerInstallation.build model S source).work ≤
      bound model S source.address (GeneralPaperEqualMeasuredRetainedPlan.sampler model S source.address source).sizes.sum :=
  (GeneralPaperStoredPreparationConstructorWork.build_work model S source hA hCap).trans
    ((GeneralPaperMeasuredPlanWorkRates.constructor_majorant model S source hA hCap).trans
      (constructor_majorant model S source hA hCap))

theorem every_returned_work {n m q : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m q}
    (model : RationalCostModel) (S : ℕ) (source : GeneralPaperEqualStoredBitSampler.Sampler G l)
    (hA : 0 < source.address)
    (hCap : (GeneralPaperEqualMeasuredRetainedPlan.sampler model S source.address source).sizes.sum < 2 ^ source.address)
    (returned : Installed source.address) (hReturn : (GeneralPaperCountedSamplerInstallation.build model S source).values = some returned) :
    returned.work ≤ bound model S source.address (GeneralPaperEqualMeasuredRetainedPlan.sampler model S source.address source).sizes.sum :=
  (GeneralPaperMeasuredPlanWorkRates.every_returned_work model S source hA hCap returned hReturn).trans
    (constructor_majorant model S source hA hCap)

theorem dominant_prefix_work {n : ℕ} (model : RationalCostModel) (S A start chosen : ℕ) (source : RationalResourceArray n)
    (rest : List (Region A)) (hA : 0 < A)
    (hCap : start + (GeneralPaperStoredDominantCursor.plan model S A chosen source).sizes.sum < 2 ^ A) :
    (GeneralPaperStoredDominantInstallation.run model S A chosen source
      ((GeneralPaperMeasuredBlockLayout.run model S A start (GeneralPaperStoredDominantCursor.plan model S A chosen source)).1 ++ rest)).work ≤
      ((GeneralPaperStoredDominantCursor.plan model S A chosen source).sizes.sum + 1) * 48 * unit model S A +
        GeneralPaperStoredDirectoryPreparationWork.bound model S A (GeneralPaperStoredDominantCursor.plan model S A chosen source).sizes.sum := by
  obtain ⟨hParsed,_,hSafe,hCovered⟩ := GeneralPaperStoredDominantCursor.success model S A start chosen source rest
  have hCursor := GeneralPaperCompleteSamplerCursorWork.dominant model S A start chosen source rest hA hCap
  have hFinish := GeneralPaperStoredDirectoryPreparationWork.finish_work model S A start
    (GeneralPaperStoredDominantCursor.run S A chosen source
      ((GeneralPaperMeasuredBlockLayout.run model S A start (GeneralPaperStoredDominantCursor.plan model S A chosen source)).1 ++ rest)).work
    (GeneralPaperStoredDominantCursor.plan model S A chosen source)
    (GeneralPaperStoredDominantCursor.expected model S A chosen source start) hSafe hCovered
    (GeneralPaperStoredDominantCursor.positive model S A chosen source hA) hA hCap
  simp only [GeneralPaperStoredDominantInstallation.run,hParsed]
  omega

theorem every_dominant_prefix_returned {n : ℕ} (model : RationalCostModel) (S A start chosen : ℕ) (source : RationalResourceArray n)
    (rest : List (Region A)) (hA : 0 < A)
    (hCap : start + (GeneralPaperStoredDominantCursor.plan model S A chosen source).sizes.sum < 2 ^ A)
    (returned : Installed A)
    (hReturn : (GeneralPaperStoredDominantInstallation.run model S A chosen source
      ((GeneralPaperMeasuredBlockLayout.run model S A start (GeneralPaperStoredDominantCursor.plan model S A chosen source)).1 ++ rest)).values = some returned) :
    returned.work ≤ ((GeneralPaperStoredDominantCursor.plan model S A chosen source).sizes.sum + 1) * 48 * unit model S A +
      GeneralPaperStoredDirectoryPreparationWork.bound model S A (GeneralPaperStoredDominantCursor.plan model S A chosen source).sizes.sum := by
  obtain ⟨actual,hActual,_,hWork,_,_⟩ := GeneralPaperStoredDominantInstallation.source model S A start chosen source rest hA hCap
  have hSame : actual = returned := Option.some.inj (hActual.symm.trans hReturn)
  rw [← hSame,hWork]
  exact dominant_prefix_work model S A start chosen source rest hA hCap

@[fun_prop]
theorem rate {α : Type*} (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model)
    (S A B r L : α → ℕ) (hL : ∀ x,1 ≤ L x) (hr : ∀ x,1 ≤ r x)
    (hS : Tight S L) (hA : Tight A L) (hExtent : Bound B r L) :
    Bound (fun x => bound model (S x) (A x) (B x)) r L := by
  have hSP := polylog_of_tight hS
  have hAP := polylog_of_tight hA
  have hUnit := GeneralPaperMeasuredPlanWorkRates.unit_rate model hFast S A L hL hS hA
  have hStep := GeneralPaperStoredPreparationWorkRates.layout_step_rate model hFast S A L hL hS hA
  have hDirectory := GeneralPaperStoredPreparationWorkRates.directory_rate model hFast S A B r L hL hr hS hA hExtent
  unfold bound
  fun_prop

theorem build_rate {α : Type*} {n m q : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m q}
    (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model)
    (S r L : α → ℕ) (sources : α → GeneralPaperEqualStoredBitSampler.Sampler G l)
    (hL : ∀ x,1 ≤ L x) (hr : ∀ x,1 ≤ r x) (hS : Tight S L)
    (hA : Tight (fun x => (sources x).address) L)
    (hCap : ∀ x,(GeneralPaperEqualMeasuredRetainedPlan.sampler model (S x) (sources x).address (sources x)).sizes.sum < 2 ^ (sources x).address)
    (hExtent : Bound (fun x => (GeneralPaperEqualMeasuredRetainedPlan.sampler model (S x) (sources x).address (sources x)).sizes.sum) r L) :
    Bound (fun x => (GeneralPaperCountedSamplerInstallation.build model (S x) (sources x)).work) r L := by
  have hMajor := rate model hFast S (fun x => (sources x).address)
    (fun x => (GeneralPaperEqualMeasuredRetainedPlan.sampler model (S x) (sources x).address (sources x)).sizes.sum)
    r L hL hr hS hA hExtent
  exact dominated hMajor (fun x => build_work model (S x) (sources x)
    (GeneralPaperStoredNativeConstruction.address_positive (sources x)) (hCap x))

end Blotto.GeneralPaperCompleteInnerPreparationWork
