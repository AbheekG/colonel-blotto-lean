import Blotto.GeneralPaperNativeWorkingResourceRates

/-! Native selected-cache and description storage with the sharp additive
working-space rate. Only the actually executed circle branch contributes. -/
namespace Blotto.GeneralPaperNativeWorkingDescriptionRates
open GeneralPaperNativeResourceDomain GeneralPaperNativeResourceParameters GeneralPaperNativeResourceReferenceGrowth
open GeneralPaperUniformResourceGrowth GeneralPaperNativeWorkingResourceRates
open GeneralPaperEncodedScalarStorage GeneralPaperEncodedBasisStorage
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 16384

theorem common_extra_rate {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d) :
    Bound (fun p => GeneralPaperCacheConstructionGrowth.extraProfile model 1 p.n (reduced model p).classified.light.size
      (reduced model p).representatives (reduced model p).classified.lightWeight) (rate model) (logarithm model) := by
  have hL := logarithm_positive model
  have hR := rate_positive model
  unfold GeneralPaperCacheConstructionGrowth.extraProfile GeneralPaperSharedCacheConstructionStorage.lightScalarProfile
    GeneralPaperSharedCacheConstructionStorage.profile GeneralPaperCircleCoefficientConstructionStorage.profile
    GeneralPaperCircleCoefficientConstructionStorage.scalarProfile GeneralPaperCircleCoefficientConstructionStorage.scalarCap
    GeneralPaperCircleCoefficientConstructionStorage.metadataCap GeneralPaperCircleCoefficientConstructionStorage.price
    GeneralPaperCircleCoefficientConstructionStorage.callbackPrice GeneralPaperCircleRationalCoefficients.width
    GeneralPaperCircleArcConstructionStorage.profile GeneralPaperCircleArcConstructionStorage.frameProfile
    GeneralPaperCircleArcConstructionStorage.cap GeneralPaperCircleArcConstructionStorage.price
    GeneralPaperSharedCacheConstructionStorage.cap GeneralPaperSharedCacheConstructionStorage.price
    GeneralPaperSharedCacheConstructionStorage.magnitude GeneralPaperNativePayloadFillStorage.workCap
    GeneralPaperStockListPayloadStorage.ofFnProfile GeneralPaperCachedCircleRetainedStorage.commonProfile
  dsimp only [GeneralPaperCircleCoefficientConstructionStorage.price,GeneralPaperCircleCoefficientConstructionStorage.callbackPrice,
    GeneralPaperCircleRationalCoefficients.width,GeneralPaperCircleArcConstructionStorage.price,
    GeneralPaperSharedCacheConstructionStorage.magnitude,GeneralPaperNativePayloadFillStorage.workCap]
  fun_prop (config := {maxSteps := 4000})


def layout (model : RationalCostModel) (p : Problem) : ℕ :=
  2*GeneralPaperEnclosingSourceOwners.columnsProfile 1 (rows model p) (reduced model p).m (labels model p) (1+2*height model p)+
    2*GeneralPaperCachedCircleRetainedStorage.referenceRowsProfile 1 (rows model p) (reduced model p).m+128

theorem layout_rate {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d) :
    Bound (layout model) (rate model) (logarithm model) := by
  have hL := logarithm_positive model
  have hR := rate_positive model
  have hRows := row_rate hg
  apply dominated (g:=fun p => 2*rowEnvelope model p+64) (by fun_prop)
  intro p
  have hLayout := GeneralPaperStrategyDescriptionProfileRates.layout_le model 1 (rows model p) (reduced model p).m (labels model p) (height model p)
  have hMono := GeneralPaperSortedConstructionProfileRates.parameters_mono model 1 (rows model p) (rows model p)
    0 (reduced model p).m (reduced model p).m (reduced model p).m (labels model p) (labels model p)
    (1+2*height model p) (1+2*height model p) le_rfl (Nat.zero_le _) le_rfl le_rfl le_rfl
  change layout model p≤2*GeneralPaperCachedRowConstructionStorage.profile model 1 (rows model p) 0 (reduced model p).m
    (labels model p) (1+2*height model p)+64 at hLayout
  change _≤rowEnvelope model p at hMono
  omega

theorem physical_rate {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d) :
    Bound (fun p => GeneralPaperStrategyDescriptionConstructionStorage.physicalProfile 1 (rows model p)
      (reduced model p).m (labels model p) (height model p)) (rate model) (logarithm model) := by
  apply dominated (layout_rate hg)
  intro p
  unfold layout GeneralPaperStrategyDescriptionConstructionStorage.physicalProfile
  omega

theorem description_return_rate {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d) :
    Bound (fun p => GeneralPaperClosedDescriptionStorage.descriptionProfile 1 (rows model p) (labels model p)
      (height model p) (reduced model p)) (rate model) (logarithm model) := by
  have hL := logarithm_positive model
  have hR := rate_positive model
  have hCommon : Bound (fun p => GeneralPaperCachedCircleRetainedStorage.commonProfile 1 (reduced model p).classified.light.size
      (reduced model p).representatives (reduced model p).classified.lightWeight) (rate model) (logarithm model) := by
    unfold GeneralPaperCachedCircleRetainedStorage.commonProfile
    fun_prop (config := {maxSteps := 4000})
  have hLayout := layout_rate hg
  apply dominated (bound_add _ _ _ _ hL hCommon hLayout)
  intro p
  unfold GeneralPaperClosedDescriptionStorage.descriptionProfile layout
  omega

theorem selected_child_rate {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d) :
    Bound (fun p => GeneralPaperStrategyDescriptionConstructionStorage.childProfile model 1 (rows model p) (labels model p)
      (height model p) (reduced model p)) (rate model) (logarithm model) := by
  have hL := logarithm_positive model
  have hR := rate_positive model
  have hOwner := owner_rate model
  have hCommon := common_extra_rate hg
  have hRows := row_rate hg
  have hCap := cache_cap_small hg
  apply dominated (g:=fun p => GeneralPaperOriginalReductionRetainedStorage.footprint 1 (reduced model p)+
    2*GeneralPaperCacheConstructionGrowth.extraProfile model 1 p.n (reduced model p).classified.light.size
      (reduced model p).representatives (reduced model p).classified.lightWeight+
    4*rowEnvelope model p+9*(natBits (GeneralPaperCachedPairConstructionStorage.cap model 1 (rows model p) (height model p) (reduced model p))+1)+192)
    (by fun_prop (config := {maxSteps := 4000}))
  intro p
  unfold GeneralPaperStrategyDescriptionConstructionStorage.childProfile
  split_ifs with he
  · have hm := (GeneralPaperNativeReductionShape.original_shape false model 1 (exponent p) p.values he).1
    change (reduced model p).m=(reduced model p).classified.heavy.size+(reduced model p).representatives at hm
    have hRowsBound := GeneralPaperSortedConstructionProfileRates.parameters_mono model 1 (rows model p) (rows model p)
      (reduced model p).classified.heavy.size (reduced model p).m (reduced model p).representatives (reduced model p).m
      (labels model p) (labels model p) (1+2*height model p) (1+2*height model p)
      le_rfl (by omega) (by omega) le_rfl le_rfl
    have hBound := GeneralPaperCacheConstructionGrowth.pair_profile_bound model 1 (rows model p) (labels model p) (height model p) (reduced model p)
    change _≤GeneralPaperOriginalReductionRetainedStorage.footprint 1 (reduced model p)+
      2*GeneralPaperCacheConstructionGrowth.extraProfile model 1 p.n (reduced model p).classified.light.size
        (reduced model p).representatives (reduced model p).classified.lightWeight+
      4*rowEnvelope model p+9*(natBits (GeneralPaperCachedPairConstructionStorage.cap model 1 (rows model p) (height model p) (reduced model p))+1)+192
    unfold rowEnvelope
    omega
  · exact Nat.zero_le _

theorem description_rate {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d) :
    Bound (fun p => GeneralPaperStrategyDescriptionConstructionStorage.profile model 1 (rows model p) (labels model p)
      (height model p) (reduced model p)) (rate model) (logarithm model) := by
  have hL := logarithm_positive model
  have hR := rate_positive model
  have hOwner := owner_rate model
  have hPhysical := physical_rate hg
  have hReturn := description_return_rate hg
  have hChild := selected_child_rate hg
  have hPrice := description_price_small hg
  have hCap : Small (fun p => GeneralPaperStrategyDescriptionConstructionStorage.cap model 1 (rows model p) (labels model p)
      (height model p) (reduced model p)) (logarithm model) := by
    unfold GeneralPaperStrategyDescriptionConstructionStorage.cap
    fun_prop
  unfold GeneralPaperStrategyDescriptionConstructionStorage.profile
  fun_prop (config := {maxSteps := 4000})

end Blotto.GeneralPaperNativeWorkingDescriptionRates
