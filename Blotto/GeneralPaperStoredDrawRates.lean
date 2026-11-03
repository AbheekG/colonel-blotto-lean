import Blotto.GeneralPaperStoredDrawRateAlgebra

/-! Complete stored grouped draw rates retain one linear operand-precision
factor and one output-length factor. Address metadata contributes only
polylogarithmic factors; fresh-bit count is not assumed logarithmic. -/
namespace Blotto.GeneralPaperStoredDrawRates
open GeneralPaperUniformResourceGrowth GeneralPaperEqualUniformRateAlgebra GeneralPaperStoredDrawRateAlgebra
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192

theorem coordinate_rate {α : Type*} (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model)
    (A s r L : α → ℕ) (hL : ∀ x,1 ≤ L x) (hr : ∀ x,1 ≤ r x) (hA : Tight A L) (hs : Bound s r L) (hss : Small s L) :
    Bound (fun x => GeneralPaperStoredRouteCoordinateWork.bound model (A x) 3 (s x)) r L := by
  have hAP := polylog_of_tight hA
  have hReference : Bound (fun x => GeneralPaperStoredReferenceReadWork.readBound model (A x) (A x)) r L :=
    rate_mono (GeneralPaperStoredReadWorkRates.reference_rate model hFast A L hL hA) hr
  have hScalar : Bound (fun x => GeneralPaperStoredScalarReadWork.overhead model (A x)) r L :=
    rate_mono (GeneralPaperStoredReadWorkRates.scalar_overhead_rate model hFast A L hL hA) hr
  have hOperands : Bound (fun x => 1 + 4 * s x) r L := by fun_prop
  have hOperandSmall : Small (fun x => 1 + 4 * s x) L := by fun_prop
  have hArithmetic := rational_bound model hFast _ r L hL hOperands hOperandSmall
  unfold GeneralPaperStoredRouteCoordinateWork.bound GeneralPaperStoredRouteArrayWork.heightBound
  fun_prop

theorem emission_rate {α : Type*} (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model)
    (A n s r L : α → ℕ) (hL : ∀ x,1 ≤ L x) (hr : ∀ x,1 ≤ r x) (hA : Tight A L) (hs : Bound s r L) (hss : Small s L) :
    Bound (fun x => GeneralPaperStoredEmissionWork.samplerBound model (A x) (n x) 3 (s x)) (fun x => (n x + 1) * r x) L := by
  have hAP := polylog_of_tight hA
  have hTotal : ∀ x,1 ≤ (n x + 1) * r x := fun x => (hr x).trans (by simpa only [Nat.one_mul] using Nat.mul_le_mul_right (r x) (by omega : 1 ≤ n x + 1))
  have hCoordinate := coordinate_rate model hFast A s r L hL hr hA hs hss
  have hStep : Bound (fun x => GeneralPaperStoredStreamWork.stepBound model (A x)) r L :=
    rate_mono (GeneralPaperStoredReadWorkRates.step_rate model hFast A L hL hA) hr
  have hChunk : Bound (fun x => GeneralPaperStoredRouteCoordinateWork.bound model (A x) 3 (s x) +
      GeneralPaperStoredStreamWork.stepBound model (A x) + 128 * (A x + 1) + (1 + 4 * s x)) r L := by fun_prop
  have hN : Bound n (fun x => n x + 1) L := pointwise _ _ _ 1 (fun x => by omega)
  have hProduct := bound_mul hN hChunk
  have hArray : Bound (fun x => 64 * (n x + 1) * A x) (fun x => n x + 1) L := by
    have hNPlus : Bound (fun x => n x + 1) (fun x => n x + 1) L := pointwise _ _ _ 1 (fun x => by omega)
    have hNPos : ∀ x,1 ≤ n x + 1 := fun x => by omega
    fun_prop
  have hArrayTotal : Bound (fun x => 64 * (n x + 1) * A x) (fun x => (n x + 1) * r x) L :=
    rate_mono hArray (fun x => by simpa only [Nat.mul_one] using Nat.mul_le_mul_left (n x + 1) (hr x))
  have hCount : Bound (fun x => GeneralPaperStoredCountReadWork.bound model (A x)) (fun x => (n x + 1) * r x) L :=
    rate_mono (GeneralPaperStoredReadWorkRates.count_rate model hFast A L hL hA) hTotal
  have hReference : Bound (fun x => GeneralPaperStoredReferenceReadWork.readBound model (A x) (A x)) (fun x => (n x + 1) * r x) L :=
    rate_mono (GeneralPaperStoredReadWorkRates.reference_rate model hFast A L hL hA) hTotal
  unfold GeneralPaperStoredEmissionWork.samplerBound GeneralPaperStoredEmissionWork.preparedBound
    GeneralPaperStoredRouteEmissionWork.bound GeneralPaperStoredRouteEmissionWork.collectBound
  fun_prop

theorem groups_rate {α : Type*} (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model)
    (A s b K r L : α → ℕ) (hL : ∀ x,1 ≤ L x) (hr : ∀ x,1 ≤ r x) (hA : Tight A L)
    (hs : Bound s r L) (hss : Small s L) (hb : Bound b r L) (hbs : Small b L) (hK : Bound K r L) (hKs : Small K L) :
    Bound (fun x => GeneralPaperStoredSamplerGroupsWork.runBound model (A x) 3 (s x) (b x) (K x)) r L := by
  have hAP := polylog_of_tight hA
  have hBase : Bound (fun x => GeneralPaperEqualBitGroups.base (s x) (b x) (K x)) r L := by unfold GeneralPaperEqualBitGroups.base; fun_prop
  have hBaseSmall : Small (fun x => GeneralPaperEqualBitGroups.base (s x) (b x) (K x)) L := by unfold GeneralPaperEqualBitGroups.base; fun_prop
  have hOperands : Bound (fun x => 1 + 2 * expressionHeightBudget (GeneralPaperEqualBitGroups.base (s x) (b x) (K x)) 3) r L := by fun_prop
  have hOperandSmall : Small (fun x => 1 + 2 * expressionHeightBudget (GeneralPaperEqualBitGroups.base (s x) (b x) (K x)) 3) L := by fun_prop
  have hArithmetic := rational_bound model hFast _ r L hL hOperands hOperandSmall
  have hPerElement : Bound (fun x => GeneralPaperStoredRationalCollectionWork.perElement model (A x)) r L :=
    rate_mono (GeneralPaperStoredReadWorkRates.per_element_rate model hFast A L hL hA) hr
  have hCount : Bound (fun x => GeneralPaperStoredCountReadWork.bound model (A x)) r L :=
    rate_mono (GeneralPaperStoredReadWorkRates.count_rate model hFast A L hL hA) hr
  have hReference : Bound (fun x => GeneralPaperStoredReferenceReadWork.readBound model (A x) (A x)) r L :=
    rate_mono (GeneralPaperStoredReadWorkRates.reference_rate model hFast A L hL hA) hr
  have hScalar : Bound (fun x => GeneralPaperStoredScalarReadWork.overhead model (A x)) r L :=
    rate_mono (GeneralPaperStoredReadWorkRates.scalar_overhead_rate model hFast A L hL hA) hr
  unfold GeneralPaperStoredSamplerGroupsWork.runBound GeneralPaperStoredPreparedGroupsWork.bound
    GeneralPaperStoredEndpointWork.heightBound GeneralPaperStoredInterpolationWork.bound GeneralPaperStoredInterpolationWork.perElement
  fun_prop

theorem fixed_groups_rate {α : Type*} (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model)
    (A n w P K s b c r L : α → ℕ) (hL : ∀ x,1 ≤ L x) (hr : ∀ x,1 ≤ r x) (hA : Tight A L)
    (hw : Bound w r L) (hP : Bound P r L) (hK : Bound K r L) (hKs : Small K L)
    (hs : Bound s r L) (hss : Small s L) (hb : Bound b r L) (hbs : Small b L) (hc : Bound c r L) (hcs : Small c L) :
    Bound (fun x => GeneralPaperStoredDrawMajorant.bound model (A x) (n x) 3 (w x) (P x) (K x) (s x) (b x) (c x))
      (fun x => (n x + 1) * r x) L := by
  have hAP := polylog_of_tight hA
  have hTotal : ∀ x,1 ≤ (n x + 1) * r x := fun x => (hr x).trans (by simpa only [Nat.one_mul] using Nat.mul_le_mul_right (r x) (by omega : 1 ≤ n x + 1))
  have hRTotal : ∀ x,r x ≤ (n x + 1) * r x := fun x => by simpa only [Nat.one_mul] using Nat.mul_le_mul_right (r x) (by omega : 1 ≤ n x + 1)
  have hRejection := rate_mono (GeneralPaperStoredRejectionWorkRates.fixed_count_rate model hFast A w r L hL hr hA hw) hRTotal
  have hMidpoint := rate_mono (midpoint_rate model hFast A P K r L hL hr hA hP hK hKs) hRTotal
  have hGroups := rate_mono (groups_rate model hFast A s b K r L hL hr hA hs hss hb hbs hK hKs) hRTotal
  have hHeight : Bound (fun x => GeneralPaperStoredPostselectionWork.emissionHeight (s x) (b x) (c x) (K x)) r L := by
    unfold GeneralPaperStoredPostselectionWork.emissionHeight GeneralPaperEqualCachedEmission.scaledHeight GeneralPaperEqualCachedEmission.groupHeight
    fun_prop
  have hHeightSmall : Small (fun x => GeneralPaperStoredPostselectionWork.emissionHeight (s x) (b x) (c x) (K x)) L := by
    unfold GeneralPaperStoredPostselectionWork.emissionHeight GeneralPaperEqualCachedEmission.scaledHeight GeneralPaperEqualCachedEmission.groupHeight
    fun_prop
  have hEmission := emission_rate model hFast A n _ r L hL hr hA hHeight hHeightSmall
  unfold GeneralPaperStoredDrawMajorant.bound
  fun_prop

end Blotto.GeneralPaperStoredDrawRates
