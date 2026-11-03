import Blotto.GeneralPaperMeasuredRetainedPlanWork

/-! Uniform fast-bit rates for actual measured plans and their executed
layouts. The complete native sampler plan discharges the earlier supplied
plan-price hypothesis. Actual constructor prices retain exactly one cursor
pass, whose sharp price is a separate remaining obligation. -/
namespace Blotto.GeneralPaperMeasuredPlanWorkRates
open GeneralPaperMeasuredPlanWorkAlgebra
open GeneralPaperUniformResourceGrowth GeneralPaperEqualUniformRateAlgebra
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192

@[fun_prop]
theorem unit_rate {α : Type*} (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model)
    (S A L : α → ℕ) (hL : ∀ x,1 ≤ L x) (hS : Tight S L) (hA : Tight A L) :
    Polylog (fun x => unit model (S x) (A x)) L := by
  have hSP := polylog_of_tight hS
  have hAP := polylog_of_tight hA
  have hAS := small_of_tight hA hL
  unfold unit
  fun_prop

theorem work_rate {α : Type*} (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model)
    (S A r L : α → ℕ) (C : ℕ) (plans : α → GeneralPaperMeasuredBlockPlan.Plan)
    (hL : ∀ x,1 ≤ L x) (hr : ∀ x,1 ≤ r x) (hS : Tight S L) (hA : Tight A L)
    (hGood : ∀ x,Good model (S x) (A x) C (plans x))
    (hCap : ∀ x,(plans x).sizes.sum < 2 ^ A x)
    (hExtent : Bound (fun x => (plans x).sizes.sum) r L) :
    Bound (fun x => (plans x).work) r L := by
  have hUnit := unit_rate model hFast S A L hL hS hA
  have hMajor : Bound (fun x => ((plans x).sizes.sum + 1) * C * unit model (S x) (A x)) r L := by fun_prop
  exact dominated hMajor (fun x => (hGood x).2 (hCap x))

theorem layout_rate {α : Type*} (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model)
    (S A start r L : α → ℕ) (C : ℕ) (plans : α → GeneralPaperMeasuredBlockPlan.Plan)
    (hL : ∀ x,1 ≤ L x) (hr : ∀ x,1 ≤ r x) (hS : Tight S L) (hA : Tight A L)
    (hGood : ∀ x,Good model (S x) (A x) C (plans x))
    (hAPos : ∀ x,0 < A x) (hCap : ∀ x,start x + (plans x).sizes.sum < 2 ^ A x)
    (hExtent : Bound (fun x => (plans x).sizes.sum) r L) :
    Bound (fun x => (GeneralPaperMeasuredBlockLayout.run model (S x) (A x) (start x) (plans x)).2.2) r L := by
  have hWork := work_rate model hFast S A r L C plans hL hr hS hA hGood (fun x => by have h := hCap x; omega) hExtent
  exact GeneralPaperStoredPreparationWorkRates.layout_rate model hFast S A start r L plans hL hr hS hA hWork hExtent
    (fun x => (hGood x).1) hAPos hCap

def constructorBound (model : RationalCostModel) (S A B cursorWork : ℕ) : ℕ :=
  (B + 1) * 1909 * unit model S A + (B + 1) * GeneralPaperSequentialLayout.stepPrice model S A +
    cursorWork + GeneralPaperStoredDirectoryPreparationWork.bound model S A B + 128 * (S + A + 1)

@[fun_prop]
theorem constructor_rate {α : Type*} (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model)
    (S A B cursorWork r L : α → ℕ) (hL : ∀ x,1 ≤ L x) (hr : ∀ x,1 ≤ r x)
    (hS : Tight S L) (hA : Tight A L) (hExtent : Bound B r L) (hCursor : Bound cursorWork r L) :
    Bound (fun x => constructorBound model (S x) (A x) (B x) (cursorWork x)) r L := by
  have hSP := polylog_of_tight hS
  have hAP := polylog_of_tight hA
  have hUnit := unit_rate model hFast S A L hL hS hA
  have hStep := GeneralPaperStoredPreparationWorkRates.layout_step_rate model hFast S A L hL hS hA
  have hDirectory := GeneralPaperStoredPreparationWorkRates.directory_rate model hFast S A B r L hL hr hS hA hExtent
  unfold constructorBound
  fun_prop

theorem sampler_work {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
    (model : RationalCostModel) (S A : ℕ) (source : GeneralPaperEqualStoredBitSampler.Sampler G l)
    (hA : 0 < A) (hCap : GeneralPaperEqualRetainedStorage.footprint A source < 2 ^ A) :
    (GeneralPaperEqualMeasuredRetainedPlan.sampler model S A source).work ≤
      (GeneralPaperEqualRetainedStorage.footprint A source + 1) * 1909 * unit model S A := by
  have h := (GeneralPaperMeasuredRetainedPlanWork.sampler model S A source hA).2
    (by rw [GeneralPaperEqualMeasuredRetainedPlan.sampler_sum]; exact hCap)
  simpa only [GeneralPaperEqualMeasuredRetainedPlan.sampler_sum] using h

theorem constructor_majorant {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
    (model : RationalCostModel) (S : ℕ) (source : GeneralPaperEqualStoredBitSampler.Sampler G l)
    (hA : 0 < source.address)
    (hCap : (GeneralPaperEqualMeasuredRetainedPlan.sampler model S source.address source).sizes.sum < 2 ^ source.address) :
    GeneralPaperStoredPreparationConstructorWork.buildBound model S source ≤
      constructorBound model S source.address (GeneralPaperEqualMeasuredRetainedPlan.sampler model S source.address source).sizes.sum
        (GeneralPaperSamplerRecordCursor.run model S source.address source
          (GeneralPaperMeasuredBlockLayout.run model S source.address 0 (GeneralPaperEqualMeasuredRetainedPlan.sampler model S source.address source)).1).work := by
  have hPlan := (GeneralPaperMeasuredRetainedPlanWork.sampler model S source.address source hA).2 hCap
  unfold GeneralPaperStoredPreparationConstructorWork.buildBound constructorBound
  dsimp only
  omega

theorem every_returned_work {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
    (model : RationalCostModel) (S : ℕ) (source : GeneralPaperEqualStoredBitSampler.Sampler G l)
    (hA : 0 < source.address)
    (hCap : (GeneralPaperEqualMeasuredRetainedPlan.sampler model S source.address source).sizes.sum < 2 ^ source.address)
    (returned : GeneralPaperUnifiedDirectoryInstallation.Installed source.address)
    (hReturn : (GeneralPaperCountedSamplerInstallation.build model S source).values = some returned) :
    returned.work ≤ constructorBound model S source.address
      (GeneralPaperEqualMeasuredRetainedPlan.sampler model S source.address source).sizes.sum
      (GeneralPaperSamplerRecordCursor.run model S source.address source
        (GeneralPaperMeasuredBlockLayout.run model S source.address 0 (GeneralPaperEqualMeasuredRetainedPlan.sampler model S source.address source)).1).work :=
  (GeneralPaperStoredPreparationConstructorWork.every_returned_work model S source hA hCap returned hReturn).trans
    (constructor_majorant model S source hA hCap)

end Blotto.GeneralPaperMeasuredPlanWorkRates
