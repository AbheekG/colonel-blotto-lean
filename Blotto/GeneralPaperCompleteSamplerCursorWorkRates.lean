import Blotto.GeneralPaperNativeInnerPreparationWork

/-! Uniform fast-bit rates for complete actual grouped-sampler and dominant
directory extraction. Concrete cursor bounds discharge all component cost
premises; only measured extent and logarithmic metadata scaling remain. -/
namespace Blotto.GeneralPaperCompleteSamplerCursorWorkRates
open GeneralPaperSequentialLayout GeneralPaperMeasuredPlanWorkAlgebra
open GeneralPaperUniformResourceGrowth GeneralPaperEqualUniformRateAlgebra
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192

theorem sampler {α : Type*} {n m q : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m q}
    (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model)
    (S A start r L : α → ℕ) (sources : α → GeneralPaperEqualStoredBitSampler.Sampler G l)
    (rest : (x : α) → List (Region (A x)))
    (hL : ∀ x,1 ≤ L x) (hr : ∀ x,1 ≤ r x) (hS : Tight S L) (hA : Tight A L)
    (hAPos : ∀ x,0 < A x)
    (hCap : ∀ x,start x + (GeneralPaperEqualMeasuredRetainedPlan.sampler model (S x) (A x) (sources x)).sizes.sum < 2 ^ A x)
    (hExtent : Bound (fun x => (GeneralPaperEqualMeasuredRetainedPlan.sampler model (S x) (A x) (sources x)).sizes.sum) r L) :
    Bound (fun x => (GeneralPaperSamplerRecordCursor.run model (S x) (A x) (sources x)
      ((GeneralPaperMeasuredBlockLayout.run model (S x) (A x) (start x)
        (GeneralPaperEqualMeasuredRetainedPlan.sampler model (S x) (A x) (sources x))).1 ++ rest x)).work) r L := by
  have hUnit := GeneralPaperMeasuredPlanWorkRates.unit_rate model hFast S A L hL hS hA
  have hMajor : Bound (fun x => ((GeneralPaperEqualMeasuredRetainedPlan.sampler model (S x) (A x) (sources x)).sizes.sum + 1) *
      168 * unit model (S x) (A x)) r L := by fun_prop
  exact dominated hMajor (fun x => GeneralPaperCompleteSamplerCursorWork.sampler model (S x) (A x) (start x) (sources x) (rest x) (hAPos x) (hCap x))

theorem dominant {α : Type*} {n : ℕ} (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model)
    (S A start chosen r L : α → ℕ) (sources : α → RationalResourceArray n)
    (rest : (x : α) → List (Region (A x)))
    (hL : ∀ x,1 ≤ L x) (hr : ∀ x,1 ≤ r x) (hS : Tight S L) (hA : Tight A L)
    (hAPos : ∀ x,0 < A x)
    (hCap : ∀ x,start x + (GeneralPaperStoredDominantCursor.plan model (S x) (A x) (chosen x) (sources x)).sizes.sum < 2 ^ A x)
    (hExtent : Bound (fun x => (GeneralPaperStoredDominantCursor.plan model (S x) (A x) (chosen x) (sources x)).sizes.sum) r L) :
    Bound (fun x => (GeneralPaperStoredDominantCursor.run (S x) (A x) (chosen x) (sources x)
      ((GeneralPaperMeasuredBlockLayout.run model (S x) (A x) (start x)
        (GeneralPaperStoredDominantCursor.plan model (S x) (A x) (chosen x) (sources x))).1 ++ rest x)).work) r L := by
  have hUnit := GeneralPaperMeasuredPlanWorkRates.unit_rate model hFast S A L hL hS hA
  have hMajor : Bound (fun x => ((GeneralPaperStoredDominantCursor.plan model (S x) (A x) (chosen x) (sources x)).sizes.sum + 1) *
      48 * unit model (S x) (A x)) r L := by fun_prop
  exact dominated hMajor (fun x => GeneralPaperCompleteSamplerCursorWork.dominant model (S x) (A x) (start x) (chosen x) (sources x) (rest x) (hAPos x) (hCap x))

end Blotto.GeneralPaperCompleteSamplerCursorWorkRates
