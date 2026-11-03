import Blotto.GeneralPaperUnconditionalDescriptionPriceRates

/-! Native description construction time preserves an additive original
count. Unconditional source-based row prices and positive word scaling
apply to the exact same common word as original-value/source preparation. -/
namespace Blotto.GeneralPaperNativeDescriptionTimeRates
open GeneralPaperNativeResourceDomain GeneralPaperNativeResourceParameters GeneralPaperNativeResourceReferenceGrowth
open GeneralPaperUniformResourceGrowth GeneralPaperNativeSourceTimeRates
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384

theorem shared_at_one_rate {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d) :
    Bound (fun p => GeneralPaperSharedCacheConstructionStorage.originalPrice model 1 (reduced model p))
      (rate model) (logarithm model) := by
  have hL := logarithm_positive model
  have hR := rate_positive model
  have hLight := rate_mono (GeneralPaperNativeWorkingResourceRates.light_bound model) (working_rate_le model)
  unfold GeneralPaperSharedCacheConstructionStorage.originalPrice GeneralPaperSharedCacheConstructionStorage.price
    GeneralPaperCircleCoefficientConstructionStorage.price GeneralPaperCircleCoefficientConstructionStorage.callbackPrice
    GeneralPaperCircleArcConstructionStorage.price GeneralPaperSharedCacheConstructionStorage.magnitude
    GeneralPaperCircleRationalCoefficients.width GeneralPaperNativePayloadFillStorage.workCap
  fun_prop (config := {maxSteps := 4000})

theorem representatives_exact (model : RationalCostModel) (p : Problem) : (reduced model p).representatives=8*2^(exponent p) := by
  change (GeneralPaperOriginalValueReduction.run false model 1 (exponent p) p.values).1.representatives=_
  rw [GeneralPaperNativeReductionShape.original_representatives,GeneralPaperLightFieldReduction.representatives]

theorem rows_at_one_rate {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d) :
    Bound (fun p => GeneralPaperCachedRowConstructionStorage.price model 1 (rows model p) (reduced model p).representatives
      (1+2*height model p)) (rate model) (logarithm model) := by
  have h := pullback_source_bound (GeneralPaperUnconditionalDescriptionPriceRates.row_rate hg) (source model)
  have hRate := rate_mono (s:=rate model) h (fun p => by
    have hm := GeneralPaperSourceRateAlgebra.monomial_mono (a:=2) (b:=0) (c:=5) (a':=3) (b':=0) (c':=6) (by omega) (by omega) (by omega) (source model p)
    unfold rate
    omega)
  apply dominated hRate
  intro p
  apply le_of_eq
  rw [representatives_exact]
  rfl

theorem description_at_one_rate {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d) :
    Bound (fun p => GeneralPaperStrategyDescriptionConstructionStorage.price model 1 (rows model p) (height model p) (reduced model p))
      (rate model) (logarithm model) := by
  have hL := logarithm_positive model
  have hR := rate_positive model
  have hShared := shared_at_one_rate hg
  have hRows := rows_at_one_rate hg
  unfold GeneralPaperStrategyDescriptionConstructionStorage.price GeneralPaperCachedPairConstructionStorage.price
  fun_prop

theorem attach_at_one_rate {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d) :
    Bound (fun p => GeneralPaperOriginalStrategyConstructionStorage.attachPrice model 1 (exponent p) (height model p) (reduced model p))
      (rate model) (logarithm model) := by
  have hL := logarithm_positive model
  have hR := rate_positive model
  have hDescription := description_at_one_rate hg
  unfold GeneralPaperOriginalStrategyConstructionStorage.attachPrice
  fun_prop

theorem attach_at_common_word_rate {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d) :
    Bound (fun p => GeneralPaperOriginalStrategyConstructionStorage.attachPrice model (word model C d p) (exponent p)
      (height model p) (reduced model p)) (rate model) (logarithm model) :=
  profile_at_word (fun W p => GeneralPaperOriginalStrategyConstructionStorage.attachPrice model W (exponent p) (height model p) (reduced model p))
    (word model C d) (rate model) (logarithm model)
    (fun p => GeneralPaperOriginalStrategyConstructionStorage.attach_price_scaling model (exponent p) (height model p) (reduced model p))
    (word_positive model C d) (GeneralPaperNativeResourceReferenceGrowth.word_tight hg) (attach_at_one_rate hg)

end Blotto.GeneralPaperNativeDescriptionTimeRates
