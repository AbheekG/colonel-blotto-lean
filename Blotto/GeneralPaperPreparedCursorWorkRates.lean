import Blotto.GeneralPaperPreparedCursorWork

/-! Uniform fast-bit rates for complete actual endpoint-matrix and prepared
cache extraction. Constants do not depend on source contents or dimensions.
The following region suffix has no price; complete retained field extent
enters once, preserving additive original-budget precision. -/
namespace Blotto.GeneralPaperPreparedCursorWorkRates
open GeneralPaperSequentialLayout GeneralPaperMeasuredPlanWorkAlgebra
open GeneralPaperUniformResourceGrowth GeneralPaperEqualUniformRateAlgebra
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192

theorem matrix {α : Type*} {m q : ℕ} (model : RationalCostModel)
    (hFast : GeneralPaperFastRationalModel.IsFast model) (S A start r L : α → ℕ)
    (sources : α → FixedArrayTable q (FixedArrayTable m ℚ))
    (rest : (x : α) → List (Region (A x)))
    (hL : ∀ x,1 ≤ L x) (hr : ∀ x,1 ≤ r x) (hS : Tight S L) (hA : Tight A L)
    (hAPos : ∀ x,0 < A x)
    (hCap : ∀ x,start x + (GeneralPaperEqualMeasuredRetainedPlan.matrix model (S x) (A x) (sources x)).sizes.sum < 2 ^ A x)
    (hExtent : Bound (fun x => (GeneralPaperEqualMeasuredRetainedPlan.matrix model (S x) (A x) (sources x)).sizes.sum) r L) :
    Bound (fun x => (GeneralPaperMatrixFieldCursor.run (S x) (A x) (sources x)
      ((GeneralPaperMeasuredBlockLayout.run model (S x) (A x) (start x)
        (GeneralPaperEqualMeasuredRetainedPlan.matrix model (S x) (A x) (sources x))).1 ++ rest x)).work) r L := by
  have hUnit := GeneralPaperMeasuredPlanWorkRates.unit_rate model hFast S A L hL hS hA
  have hMajor : Bound (fun x => ((GeneralPaperEqualMeasuredRetainedPlan.matrix model (S x) (A x) (sources x)).sizes.sum + 1) *
      40 * unit model (S x) (A x)) r L := by fun_prop
  exact dominated hMajor (fun x => GeneralPaperPreparedCursorWork.matrix model (S x) (A x) (start x) (sources x) (rest x) (hAPos x) (hCap x))

theorem prepared {α : Type*} {n m q : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m q}
    (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model)
    (S A start r L : α → ℕ) (sources : α → GeneralPaperEqualPreparedCache.Prepared G l)
    (rest : (x : α) → List (Region (A x)))
    (hL : ∀ x,1 ≤ L x) (hr : ∀ x,1 ≤ r x) (hS : Tight S L) (hA : Tight A L)
    (hAPos : ∀ x,0 < A x)
    (hCap : ∀ x,start x + (GeneralPaperEqualMeasuredRetainedPlan.prepared model (S x) (A x) (sources x)).sizes.sum < 2 ^ A x)
    (hExtent : Bound (fun x => (GeneralPaperEqualMeasuredRetainedPlan.prepared model (S x) (A x) (sources x)).sizes.sum) r L) :
    Bound (fun x => (GeneralPaperPreparedRecordCursor.run (S x) (A x) (sources x)
      ((GeneralPaperMeasuredBlockLayout.run model (S x) (A x) (start x)
        (GeneralPaperEqualMeasuredRetainedPlan.prepared model (S x) (A x) (sources x))).1 ++ rest x)).work) r L := by
  have hUnit := GeneralPaperMeasuredPlanWorkRates.unit_rate model hFast S A L hL hS hA
  have hMajor : Bound (fun x => ((GeneralPaperEqualMeasuredRetainedPlan.prepared model (S x) (A x) (sources x)).sizes.sum + 1) *
      104 * unit model (S x) (A x)) r L := by fun_prop
  exact dominated hMajor (fun x => GeneralPaperPreparedCursorWork.prepared model (S x) (A x) (start x) (sources x) (rest x) (hAPos x) (hCap x))

end Blotto.GeneralPaperPreparedCursorWorkRates
