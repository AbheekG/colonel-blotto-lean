import Blotto.GeneralPaperMeasuredBooleanPlanLifetime

/-! Uniform extent-linear fast-bit rates for complete measured-plan
windows. Existing executed-work proofs derive the saved-price width;
neither a price nor a scratch oracle is supplied to the constructor.
Original scalar precision remains an additive measured extent. -/
namespace Blotto.GeneralPaperMeasuredPlanLifetimeRates
open GeneralPaperUniformResourceGrowth GeneralPaperEqualUniformRateAlgebra
open GeneralPaperMeasuredPlanLifetimeAlgebra (Good unit)
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

@[fun_prop]
theorem unit_rate {α : Type*} (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model)
    (S A Q L : α → ℕ) (hL : ∀ x,1 ≤ L x) (hS : Tight S L) (hA : Tight A L) (hQ : Small Q L) :
    Polylog (fun x => unit model (S x) (A x) (Q x)) L := by
  have hSP := polylog_of_tight hS
  have hAP := polylog_of_tight hA
  have hSSmall := small_of_tight hS hL
  have hASmall := small_of_tight hA hL
  have hCap : Small (fun x => GeneralPaperPayloadInstallationLifetime.cap (S x) (A x) (Q x)) L := by
    unfold GeneralPaperPayloadInstallationLifetime.cap
    fun_prop
  unfold unit
  fun_prop

theorem bound_rate {α : Type*} (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model)
    (S A r L : α → ℕ) (Cw Cs : ℕ) (plans : α → GeneralPaperMeasuredBlockPlan.Plan)
    (hL : ∀ x,1 ≤ L x) (hr : ∀ x,1 ≤ r x) (hS : Tight S L) (hA : Tight A L)
    (hGoodWork : ∀ x,GeneralPaperMeasuredPlanWorkAlgebra.Good model (S x) (A x) Cw (plans x))
    (hCap : ∀ x,(plans x).sizes.sum < 2 ^ A x)
    (hExtent : Bound (fun x => (plans x).sizes.sum) r L) (hrSmall : Small r L) :
    Bound (fun x => ((plans x).sizes.sum + 1) * Cs * unit model (S x) (A x) (plans x).work) r L := by
  have hWork := GeneralPaperMeasuredPlanWorkRates.work_rate model hFast S A r L Cw plans hL hr hS hA hGoodWork hCap hExtent
  have hQ := bound_small hL hWork hrSmall
  have hUnit := unit_rate model hFast S A (fun x => (plans x).work) L hL hS hA hQ
  have hMass : Bound (fun x => (plans x).sizes.sum + 1) r L := by fun_prop
  have hFactor := polylog_mul _ _ L (polylog_constant Cs L) hUnit
  simpa only [Nat.mul_assoc] using bound_mul_polylog _ _ r L hMass hFactor

theorem measured_rate {α : Type*} (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model)
    (S A r L : α → ℕ) (Cw Cs : ℕ) (plans : α → GeneralPaperMeasuredBlockPlan.Plan) (spaces : α → ℕ)
    (hL : ∀ x,1 ≤ L x) (hr : ∀ x,1 ≤ r x) (hS : Tight S L) (hA : Tight A L)
    (hGoodWork : ∀ x,GeneralPaperMeasuredPlanWorkAlgebra.Good model (S x) (A x) Cw (plans x))
    (hGoodLife : ∀ x,Good model (S x) (A x) Cs (plans x) (spaces x))
    (hCap : ∀ x,(plans x).sizes.sum < 2 ^ A x)
    (hExtent : Bound (fun x => (plans x).sizes.sum) r L) (hrSmall : Small r L) : Bound spaces r L := by
  apply dominated (bound_rate model hFast S A r L Cw Cs plans hL hr hS hA hGoodWork hCap hExtent hrSmall)
  intro x
  exact (hGoodLife x).2 _ (hCap x) le_rfl

theorem natural_rate {α : Type*} (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model)
    (S A value r L : α → ℕ) (hL : ∀ x,1 ≤ L x) (hr : ∀ x,1 ≤ r x) (hS : Tight S L) (hA : Tight A L)
    (hAPos : ∀ x,0 < A x) (hCap : ∀ x,GeneralPaperEncodedScalarStorage.natBits (value x) < 2 ^ A x)
    (hExtent : Bound (fun x => GeneralPaperEncodedScalarStorage.natBits (value x)) r L) (hrSmall : Small r L) :
    Bound (fun x => GeneralPaperMeasuredScalarPlanLifetime.naturalWindow model (S x) (value x)) r L := by
  apply measured_rate model hFast S A r L 1 4 (fun x => GeneralPaperMeasuredBlockPlan.natural model (S x) (value x)) _
    hL hr hS hA (fun x => GeneralPaperMeasuredLeafPlanWork.natural model (S x) (A x) (value x) (hAPos x))
    (fun x => GeneralPaperMeasuredScalarPlanLifetime.natural_good model (S x) (A x) (value x) (hAPos x))
  · simpa only [GeneralPaperMeasuredBlockPlan.natural_data,List.sum_cons,List.sum_nil,Nat.add_zero] using hCap
  · simpa only [GeneralPaperMeasuredBlockPlan.natural_data,List.sum_cons,List.sum_nil,Nat.add_zero] using hExtent
  · exact hrSmall

theorem rational_rate {α : Type*} (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model)
    (S A r L : α → ℕ) (value : α → ℚ) (hL : ∀ x,1 ≤ L x) (hr : ∀ x,1 ≤ r x) (hS : Tight S L) (hA : Tight A L)
    (hAPos : ∀ x,0 < A x) (hCap : ∀ x,rationalWordWidth (value x) < 2 ^ A x)
    (hExtent : Bound (fun x => rationalWordWidth (value x)) r L) (hrSmall : Small r L) :
    Bound (fun x => GeneralPaperMeasuredScalarPlanLifetime.rationalWindow model (S x) (value x)) r L := by
  apply measured_rate model hFast S A r L 1 4 (fun x => GeneralPaperMeasuredBlockPlan.rational model (S x) (value x)) _
    hL hr hS hA (fun x => GeneralPaperMeasuredLeafPlanWork.rational model (S x) (A x) (value x) (hAPos x))
    (fun x => GeneralPaperMeasuredScalarPlanLifetime.rational_good model (S x) (A x) (value x) (hAPos x))
  · simpa only [GeneralPaperMeasuredBlockPlan.rational_data,List.sum_cons,List.sum_nil,Nat.add_zero] using hCap
  · simpa only [GeneralPaperMeasuredBlockPlan.rational_data,List.sum_cons,List.sum_nil,Nat.add_zero] using hExtent
  · exact hrSmall

theorem boolean_bound_rate {α : Type*} {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
    (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model)
    (prepared : α → GeneralPaperEqualPreparedCache.Prepared G l)
    (cache : (x : α) → GeneralPaperEqualBooleanCache.Cache (prepared x)) (S A R L : α → ℕ)
    (hL : ∀ x,1 ≤ L x) (hR : ∀ x,1 ≤ R x) (hS : Tight S L) (hA : Tight A L) (hAPos : ∀ x,0 < A x)
    (hCap : ∀ x,(GeneralPaperEqualMeasuredRetainedPlan.boolean model (S x) (A x) (cache x)).sizes.sum < 2 ^ A x)
    (hExtent : Bound (fun x => (GeneralPaperEqualMeasuredRetainedPlan.boolean model (S x) (A x) (cache x)).sizes.sum) R L)
    (hRSmall : Small R L) :
    Bound (fun x => GeneralPaperMeasuredBooleanPlanLifetime.bound model (S x) (A x) (cache x)) R L :=
  bound_rate model hFast S A R L 213 690 (fun x => GeneralPaperEqualMeasuredRetainedPlan.boolean model (S x) (A x) (cache x))
    hL hR hS hA (fun x => GeneralPaperMeasuredRetainedPlanWork.boolean model (S x) (A x) (cache x) (hAPos x)) hCap hExtent hRSmall

theorem boolean_window_rate {α : Type*} {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
    (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model)
    (prepared : α → GeneralPaperEqualPreparedCache.Prepared G l)
    (cache : (x : α) → GeneralPaperEqualBooleanCache.Cache (prepared x)) (S A R L : α → ℕ)
    (hL : ∀ x,1 ≤ L x) (hR : ∀ x,1 ≤ R x) (hS : Tight S L) (hA : Tight A L) (hAPos : ∀ x,0 < A x)
    (hCap : ∀ x,(GeneralPaperEqualMeasuredRetainedPlan.boolean model (S x) (A x) (cache x)).sizes.sum < 2 ^ A x)
    (hExtent : Bound (fun x => (GeneralPaperEqualMeasuredRetainedPlan.boolean model (S x) (A x) (cache x)).sizes.sum) R L)
    (hRSmall : Small R L) :
    Bound (fun x => GeneralPaperMeasuredBooleanPlanLifetime.window model (S x) (A x) (cache x)) R L := by
  apply dominated (boolean_bound_rate model hFast prepared cache S A R L hL hR hS hA hAPos hCap hExtent hRSmall)
  intro x
  exact GeneralPaperMeasuredBooleanPlanLifetime.window_bound model (S x) (A x) (cache x) (hAPos x) (hCap x)

end Blotto.GeneralPaperMeasuredPlanLifetimeRates
