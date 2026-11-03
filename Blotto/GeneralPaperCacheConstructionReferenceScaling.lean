import Blotto.GeneralPaperCachedPairConstructionStorage

/-! Positive reference scaling for complete native cache construction
profiles. These properties apply to the exact owner/scratch/work-field
profiles, so a later global reservation can sum them before calibration. -/
namespace Blotto.GeneralPaperCacheConstructionReferenceScaling
open GeneralPaperReferenceScaling GeneralPaperEncodedBasisStorage
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 16384

@[fun_prop]
theorem fill (n : ℕ) (P C Q : ℕ → ℕ) (hp : Scale P) (hc : Scale C) (hq : Scale Q) :
    Scale (fun W => GeneralPaperNativePayloadFillStorage.profile W (P W) n (C W) (Q W)) := by
  unfold GeneralPaperNativePayloadFillStorage.profile GeneralPaperNativePayloadFillStorage.frameProfile
    GeneralPaperNativePayloadFillStorage.metadataCap GeneralPaperNativePayloadFillStorage.workCap
  fun_prop

@[fun_prop]
theorem coefficient (model : RationalCostModel) (g R mass : ℕ) :
    Scale (fun W => GeneralPaperCircleCoefficientConstructionStorage.profile model W g R mass) := by
  unfold GeneralPaperCircleCoefficientConstructionStorage.profile
    GeneralPaperCircleCoefficientConstructionStorage.scalarProfile GeneralPaperCircleCoefficientConstructionStorage.scalarCap
    GeneralPaperCircleCoefficientConstructionStorage.metadataCap GeneralPaperCircleCoefficientConstructionStorage.price
    GeneralPaperCircleCoefficientConstructionStorage.callbackPrice GeneralPaperNativePayloadFillStorage.workCap arrayProfile
  fun_prop

@[fun_prop]
theorem arc (model : RationalCostModel) (N M R : ℕ) :
    Scale (fun W => GeneralPaperCircleArcConstructionStorage.profile model W N M R) := by
  unfold GeneralPaperCircleArcConstructionStorage.profile GeneralPaperCircleArcConstructionStorage.frameProfile
    GeneralPaperCircleArcConstructionStorage.cap GeneralPaperCircleArcConstructionStorage.price
  fun_prop

@[fun_prop]
theorem common (model : RationalCostModel) (g R mass : ℕ) :
    Scale (fun W => GeneralPaperSharedCacheConstructionStorage.profile model W g R mass) := by
  unfold GeneralPaperSharedCacheConstructionStorage.profile GeneralPaperSharedCacheConstructionStorage.cap
    GeneralPaperSharedCacheConstructionStorage.price GeneralPaperCircleCoefficientConstructionStorage.price
    GeneralPaperCircleCoefficientConstructionStorage.callbackPrice GeneralPaperCircleArcConstructionStorage.price
    GeneralPaperNativePayloadFillStorage.workCap GeneralPaperStockListPayloadStorage.ofFnProfile
    GeneralPaperCachedCircleRetainedStorage.commonProfile arrayProfile
  fun_prop

@[fun_prop]
theorem original_owner {n : ℕ} (o : GeneralPaperReducedValuesDriver.Output n) :
    Scale (fun W => GeneralPaperOriginalReductionRetainedStorage.footprint W o) := by
  unfold GeneralPaperOriginalReductionRetainedStorage.footprint GeneralPaperOriginalReductionRetainedStorage.indexFoot
    GeneralPaperEncodedReferenceVector.reservedFootprint arrayFootprint
  fun_prop

@[fun_prop]
theorem original (model : RationalCostModel) {n : ℕ} (o : GeneralPaperReducedValuesDriver.Output n) :
    Scale (fun W => GeneralPaperSharedCacheConstructionStorage.originalProfile model W o) := by
  unfold GeneralPaperSharedCacheConstructionStorage.originalProfile GeneralPaperSharedCacheConstructionStorage.lightScalarProfile
    GeneralPaperSharedCacheConstructionStorage.originalPrice GeneralPaperSharedCacheConstructionStorage.price
    GeneralPaperCircleCoefficientConstructionStorage.price GeneralPaperCircleCoefficientConstructionStorage.callbackPrice
    GeneralPaperCircleArcConstructionStorage.price GeneralPaperNativePayloadFillStorage.workCap
  fun_prop

@[fun_prop]
theorem sort (model : RationalCostModel) (R H : ℕ) :
    Scale (fun W => GeneralPaperRepresentativeSortStorage.profile model W R H) := by
  unfold GeneralPaperRepresentativeSortStorage.profile
    arrayProfile GeneralPaperListReferenceConstructionStorage.profile GeneralPaperRepresentativeSortStorage.comparisonPrice
    GeneralPaperRepresentativeSortStorage.metadataCap GeneralPaperRepresentativeSortStorage.scalarProfile GeneralPaperSelectedSortStorage.profile
    GeneralPaperCeilingConstructionStorage.word GeneralPaperListReferenceConstructionStorage.frameProfile GeneralPaperRepresentativeSortStorage.compareCap
    GeneralPaperRepresentativeSortStorage.price GeneralPaperSelectedSortStorage.metadataCap GeneralPaperSortWorkMetadataStorage.profile
    GeneralPaperListReferenceConstructionStorage.metadataCap GeneralPaperNativeRepresentativeSort.profile GeneralPaperSortConstructionStorage.coefficient
    GeneralPaperSortWorkMetadataStorage.coefficient GeneralPaperListReferenceConstructionStorage.workCap GeneralPaperMergeWorkMetadataStorage.profile
    GeneralPaperPricedSort.profile GeneralPaperRankMidpointStorage.profile GeneralPaperSortConstructionStorage.controlWord
    GeneralPaperSortWorkMetadataStorage.frameProfile GeneralPaperMergeWorkMetadataStorage.frameProfile GeneralPaperQuotientConstructionStorage.frameCap
    GeneralPaperQuotientConstructionStorage.localCap GeneralPaperRankMidpointStorage.argumentHeight GeneralPaperRankMidpointStorage.metadataCap
    GeneralPaperSortConstructionStorage.controlCap GeneralPaperSortWorkMetadataStorage.metadataCap GeneralPaperFinRangeStorage.profile GeneralPaperEncodedScalarStorage.natBits
    GeneralPaperMergeWorkMetadataStorage.metadataCap GeneralPaperSortWorkMetadataStorage.workCap GeneralPaperMergeWorkMetadataStorage.workCap
    GeneralPaperSelectedSortStorage.depth GeneralPaperBoundedQuotient.heightBudget
  dsimp only
  fun_prop

@[fun_prop]
theorem sorted_reference (model : RationalCostModel) (R H : ℕ) :
    Scale (fun W => GeneralPaperSortedReferenceConstructionStorage.profile model W R H) := by
  unfold GeneralPaperSortedReferenceConstructionStorage.profile GeneralPaperSortedReferenceConstructionStorage.scalarProfile
    GeneralPaperSortedReferenceConstructionStorage.cap GeneralPaperSortedReferenceConstructionStorage.price
    GeneralPaperRepresentativeSortStorage.price GeneralPaperNativeRepresentativeSort.profile GeneralPaperPricedSort.profile
    GeneralPaperNativePayloadFillStorage.workCap
  fun_prop

@[fun_prop]
theorem row (model : RationalCostModel) (T h R K H : ℕ) :
    Scale (fun W => GeneralPaperCachedRowConstructionStorage.rowProfile model W T h R K H) := by
  unfold GeneralPaperCachedRowConstructionStorage.rowProfile GeneralPaperCachedRowConstructionStorage.representativeScalarProfile
    GeneralPaperCachedRowConstructionStorage.rowCap GeneralPaperCachedRowConstructionStorage.rowPrice
    GeneralPaperSortedReferenceConstructionStorage.price GeneralPaperRepresentativeSortStorage.price
    GeneralPaperNativeRepresentativeSort.profile GeneralPaperPricedSort.profile GeneralPaperNativePayloadFillStorage.workCap
  fun_prop

@[fun_prop]
theorem rows (model : RationalCostModel) (T h R K H : ℕ) :
    Scale (fun W => GeneralPaperCachedRowConstructionStorage.profile model W T h R K H) := by
  unfold GeneralPaperCachedRowConstructionStorage.profile GeneralPaperCachedRowConstructionStorage.tableScalarProfile
    GeneralPaperCachedRowConstructionStorage.cap GeneralPaperCachedRowConstructionStorage.price
    GeneralPaperCachedRowConstructionStorage.rowCap GeneralPaperCachedRowConstructionStorage.rowPrice
    GeneralPaperSortedReferenceConstructionStorage.price GeneralPaperRepresentativeSortStorage.price
    GeneralPaperNativeRepresentativeSort.profile GeneralPaperPricedSort.profile GeneralPaperNativePayloadFillStorage.workCap
    GeneralPaperEnclosingSourceOwners.columnsProfile GeneralPaperEnclosingSourceOwners.columnProfile arrayProfile
  fun_prop

@[fun_prop]
theorem pair (model : RationalCostModel) {n : ℕ} (T K H : ℕ) (o : GeneralPaperReducedValuesDriver.Output n) :
    Scale (fun W => GeneralPaperCachedPairConstructionStorage.profile model W T K H o) := by
  unfold GeneralPaperCachedPairConstructionStorage.profile GeneralPaperCachedPairConstructionStorage.cap
    GeneralPaperCachedPairConstructionStorage.price GeneralPaperSharedCacheConstructionStorage.originalPrice
    GeneralPaperSharedCacheConstructionStorage.price GeneralPaperCircleCoefficientConstructionStorage.price
    GeneralPaperCircleCoefficientConstructionStorage.callbackPrice GeneralPaperCircleArcConstructionStorage.price
    GeneralPaperCachedRowConstructionStorage.price GeneralPaperCachedRowConstructionStorage.rowPrice
    GeneralPaperSortedReferenceConstructionStorage.price GeneralPaperRepresentativeSortStorage.price
    GeneralPaperNativeRepresentativeSort.profile GeneralPaperPricedSort.profile GeneralPaperNativePayloadFillStorage.workCap
    GeneralPaperCachedCircleRetainedStorage.pairProfile GeneralPaperCachedCircleRetainedStorage.commonProfile
    GeneralPaperCachedCircleRetainedStorage.rowsProfile GeneralPaperCachedCircleRetainedStorage.referenceRowsProfile
    GeneralPaperEnclosingSourceOwners.columnsProfile GeneralPaperEnclosingSourceOwners.columnProfile arrayProfile
  fun_prop

end Blotto.GeneralPaperCacheConstructionReferenceScaling
