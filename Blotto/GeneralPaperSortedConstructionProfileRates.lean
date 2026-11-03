import Blotto.GeneralPaperCacheConstructionReferenceScaling

/-! Sharp growth of the actual complete sorted-row construction profiles.
The exact reference-table fill frames retain only reference arrays; native
scratch and work-field encodings are included before asymptotic rates. -/
namespace Blotto.GeneralPaperSortedConstructionProfileRates
open GeneralPaperSourceWordGrowth GeneralPaperSourceSoftBounds GeneralPaperSourceRateAlgebra
open GeneralPaperConstructedWordGrowth
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 16384

@[fun_prop]
theorem anchor_small : Small (fun x => GeneralPaperSourcePairAnchorHeights.width x.m x.k) := by
  apply GeneralPaperSourceRowsStorageRates.soft_small GeneralPaperSourcePairAnchorHeights.width_rate
  unfold monomial GeneralPaperNativeSourceRates.fields GeneralPaperNativeSourceRates.symbols GeneralPaperNativeSourceRates.accuracy
  fun_prop

def sourceProfile (model : RationalCostModel) (W m k : ℕ) : ℕ :=
  GeneralPaperCachedRowConstructionStorage.profile model W
    (GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet m k).lambda k).rows
    m m (GeneralPaperProxyParameters.prepare m k).K (1+2*GeneralPaperSourcePairAnchorHeights.width m k)

def certificate (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    Certificate (fun x => sourceProfile (GeneralPaperFastRationalMajorant.model C d) (W x) x.m x.k) := by
  have hr : Rated W 0 0 0 := poly (poly_tight W hW)
  have hs := of_tight hW
  have hA := GeneralPaperSourcePairAnchorHeights.width_rate
  have hRows := GeneralPaperSourceStaticConstructionRates.sharp_rows
  refine ⟨_,_,_,by
    unfold sourceProfile GeneralPaperCachedRowConstructionStorage.profile GeneralPaperCachedRowConstructionStorage.tableScalarProfile GeneralPaperCachedRowConstructionStorage.cap
      GeneralPaperCachedRowConstructionStorage.price GeneralPaperCachedRowConstructionStorage.rowProfile GeneralPaperCachedRowConstructionStorage.representativeScalarProfile
      GeneralPaperCachedRowConstructionStorage.rowCap GeneralPaperCachedRowConstructionStorage.rowPrice GeneralPaperSortedReferenceConstructionStorage.profile
      GeneralPaperSortedReferenceConstructionStorage.scalarProfile GeneralPaperSortedReferenceConstructionStorage.cap GeneralPaperSortedReferenceConstructionStorage.price
      GeneralPaperNativePayloadFillStorage.profile GeneralPaperNativePayloadFillStorage.frameProfile GeneralPaperNativePayloadFillStorage.metadataCap
      GeneralPaperNativePayloadFillStorage.workCap GeneralPaperEnclosingSourceOwners.columnsProfile GeneralPaperEnclosingSourceOwners.columnProfile
      GeneralPaperRepresentativeSortStorage.profile GeneralPaperEncodedBasisStorage.arrayProfile GeneralPaperListReferenceConstructionStorage.profile
      GeneralPaperRepresentativeSortStorage.comparisonPrice GeneralPaperRepresentativeSortStorage.metadataCap GeneralPaperRepresentativeSortStorage.scalarProfile
      GeneralPaperSelectedSortStorage.profile GeneralPaperCeilingConstructionStorage.word GeneralPaperListReferenceConstructionStorage.frameProfile
      GeneralPaperRepresentativeSortStorage.compareCap GeneralPaperRepresentativeSortStorage.price GeneralPaperSelectedSortStorage.metadataCap
      GeneralPaperSortWorkMetadataStorage.profile GeneralPaperListReferenceConstructionStorage.metadataCap GeneralPaperNativeRepresentativeSort.profile
      GeneralPaperSortConstructionStorage.coefficient GeneralPaperSortWorkMetadataStorage.coefficient GeneralPaperListReferenceConstructionStorage.workCap
      GeneralPaperMergeWorkMetadataStorage.profile GeneralPaperPricedSort.profile GeneralPaperRankMidpointStorage.profile
      GeneralPaperSortConstructionStorage.controlWord GeneralPaperSortWorkMetadataStorage.frameProfile GeneralPaperMergeWorkMetadataStorage.frameProfile
      GeneralPaperQuotientConstructionStorage.frameCap GeneralPaperQuotientConstructionStorage.localCap GeneralPaperRankMidpointStorage.argumentHeight
      GeneralPaperRankMidpointStorage.metadataCap GeneralPaperSortConstructionStorage.controlCap GeneralPaperSortWorkMetadataStorage.metadataCap
      GeneralPaperFinRangeStorage.profile GeneralPaperEncodedScalarStorage.natBits GeneralPaperMergeWorkMetadataStorage.metadataCap
      GeneralPaperSortWorkMetadataStorage.workCap GeneralPaperMergeWorkMetadataStorage.workCap GeneralPaperSelectedSortStorage.depth
      GeneralPaperBoundedQuotient.heightBudget
    dsimp only [GeneralPaperFastRationalMajorant.model]
    source_space⟩

theorem degrees (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    ((certificate C d W hW).fields,(certificate C d W hW).symbols,(certificate C d W hW).accuracy)=(2,0,3) := rfl

theorem model_mono (actual upper : RationalCostModel) (hPrice : ∀ n,actual.rat n≤upper.rat n)
    (W T h R K H : ℕ) :
    GeneralPaperCachedRowConstructionStorage.profile actual W T h R K H≤
      GeneralPaperCachedRowConstructionStorage.profile upper W T h R K H := by
  unfold GeneralPaperCachedRowConstructionStorage.profile GeneralPaperCachedRowConstructionStorage.tableScalarProfile GeneralPaperCachedRowConstructionStorage.cap
    GeneralPaperCachedRowConstructionStorage.price GeneralPaperCachedRowConstructionStorage.rowProfile GeneralPaperCachedRowConstructionStorage.representativeScalarProfile
    GeneralPaperCachedRowConstructionStorage.rowCap GeneralPaperCachedRowConstructionStorage.rowPrice GeneralPaperSortedReferenceConstructionStorage.profile
    GeneralPaperSortedReferenceConstructionStorage.scalarProfile GeneralPaperSortedReferenceConstructionStorage.cap GeneralPaperSortedReferenceConstructionStorage.price
    GeneralPaperNativePayloadFillStorage.profile GeneralPaperNativePayloadFillStorage.frameProfile GeneralPaperNativePayloadFillStorage.metadataCap
    GeneralPaperNativePayloadFillStorage.workCap GeneralPaperEnclosingSourceOwners.columnsProfile GeneralPaperEnclosingSourceOwners.columnProfile
    GeneralPaperRepresentativeSortStorage.profile GeneralPaperEncodedBasisStorage.arrayProfile GeneralPaperListReferenceConstructionStorage.profile
    GeneralPaperRepresentativeSortStorage.comparisonPrice GeneralPaperRepresentativeSortStorage.metadataCap GeneralPaperRepresentativeSortStorage.scalarProfile
    GeneralPaperSelectedSortStorage.profile GeneralPaperCeilingConstructionStorage.word GeneralPaperListReferenceConstructionStorage.frameProfile
    GeneralPaperRepresentativeSortStorage.compareCap GeneralPaperRepresentativeSortStorage.price GeneralPaperSelectedSortStorage.metadataCap
    GeneralPaperSortWorkMetadataStorage.profile GeneralPaperListReferenceConstructionStorage.metadataCap GeneralPaperNativeRepresentativeSort.profile
    GeneralPaperSortConstructionStorage.coefficient GeneralPaperSortWorkMetadataStorage.coefficient GeneralPaperListReferenceConstructionStorage.workCap
    GeneralPaperMergeWorkMetadataStorage.profile GeneralPaperPricedSort.profile GeneralPaperRankMidpointStorage.profile
    GeneralPaperSortConstructionStorage.controlWord GeneralPaperSortWorkMetadataStorage.frameProfile GeneralPaperMergeWorkMetadataStorage.frameProfile
    GeneralPaperQuotientConstructionStorage.frameCap GeneralPaperQuotientConstructionStorage.localCap GeneralPaperRankMidpointStorage.argumentHeight
    GeneralPaperRankMidpointStorage.metadataCap GeneralPaperSortConstructionStorage.controlCap GeneralPaperSortWorkMetadataStorage.metadataCap
    GeneralPaperFinRangeStorage.profile GeneralPaperEncodedScalarStorage.natBits GeneralPaperMergeWorkMetadataStorage.metadataCap
    GeneralPaperSortWorkMetadataStorage.workCap GeneralPaperMergeWorkMetadataStorage.workCap GeneralPaperSelectedSortStorage.depth
    GeneralPaperBoundedQuotient.heightBudget
  dsimp only
  gcongr <;> exact hPrice _

theorem parameters_mono (model : RationalCostModel) (W T T' h h' R R' K K' H H' : ℕ)
    (hT : T≤T') (hh : h≤h') (hR : R≤R') (hK : K≤K') (hH : H≤H') :
    GeneralPaperCachedRowConstructionStorage.profile model W T h R K H≤
      GeneralPaperCachedRowConstructionStorage.profile model W T' h' R' K' H' := by
  unfold GeneralPaperCachedRowConstructionStorage.profile GeneralPaperCachedRowConstructionStorage.tableScalarProfile GeneralPaperCachedRowConstructionStorage.cap
    GeneralPaperCachedRowConstructionStorage.price GeneralPaperCachedRowConstructionStorage.rowProfile GeneralPaperCachedRowConstructionStorage.representativeScalarProfile
    GeneralPaperCachedRowConstructionStorage.rowCap GeneralPaperCachedRowConstructionStorage.rowPrice GeneralPaperSortedReferenceConstructionStorage.profile
    GeneralPaperSortedReferenceConstructionStorage.scalarProfile GeneralPaperSortedReferenceConstructionStorage.cap GeneralPaperSortedReferenceConstructionStorage.price
    GeneralPaperNativePayloadFillStorage.profile GeneralPaperNativePayloadFillStorage.frameProfile GeneralPaperNativePayloadFillStorage.metadataCap
    GeneralPaperNativePayloadFillStorage.workCap GeneralPaperEnclosingSourceOwners.columnsProfile GeneralPaperEnclosingSourceOwners.columnProfile
    GeneralPaperRepresentativeSortStorage.profile GeneralPaperEncodedBasisStorage.arrayProfile GeneralPaperListReferenceConstructionStorage.profile
    GeneralPaperRepresentativeSortStorage.comparisonPrice GeneralPaperRepresentativeSortStorage.metadataCap GeneralPaperRepresentativeSortStorage.scalarProfile
    GeneralPaperSelectedSortStorage.profile GeneralPaperCeilingConstructionStorage.word GeneralPaperListReferenceConstructionStorage.frameProfile
    GeneralPaperRepresentativeSortStorage.compareCap GeneralPaperRepresentativeSortStorage.price GeneralPaperSelectedSortStorage.metadataCap
    GeneralPaperSortWorkMetadataStorage.profile GeneralPaperListReferenceConstructionStorage.metadataCap GeneralPaperNativeRepresentativeSort.profile
    GeneralPaperSortConstructionStorage.coefficient GeneralPaperSortWorkMetadataStorage.coefficient GeneralPaperListReferenceConstructionStorage.workCap
    GeneralPaperMergeWorkMetadataStorage.profile GeneralPaperPricedSort.profile GeneralPaperRankMidpointStorage.profile
    GeneralPaperSortConstructionStorage.controlWord GeneralPaperSortWorkMetadataStorage.frameProfile GeneralPaperMergeWorkMetadataStorage.frameProfile
    GeneralPaperQuotientConstructionStorage.frameCap GeneralPaperQuotientConstructionStorage.localCap GeneralPaperRankMidpointStorage.argumentHeight
    GeneralPaperRankMidpointStorage.metadataCap GeneralPaperSortConstructionStorage.controlCap GeneralPaperSortWorkMetadataStorage.metadataCap
    GeneralPaperFinRangeStorage.profile GeneralPaperEncodedScalarStorage.natBits GeneralPaperMergeWorkMetadataStorage.metadataCap
    GeneralPaperSortWorkMetadataStorage.workCap GeneralPaperMergeWorkMetadataStorage.workCap GeneralPaperSelectedSortStorage.depth
    GeneralPaperBoundedQuotient.heightBudget
  dsimp only
  gcongr <;> exact model.monotone (by gcongr)

theorem native_profile {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d)
    (W : Input → ℕ) (hW : Tight W) (h R : Input → ℕ) (hh : ∀ x,h x≤x.m) (hR : ∀ x,R x≤x.m) :
    Rated (fun x => GeneralPaperCachedRowConstructionStorage.profile model (W x)
      (GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet x.m x.k).lambda x.k).rows
      (h x) (R x) (GeneralPaperProxyParameters.prepare x.m x.k).K (1+2*GeneralPaperSourcePairAnchorHeights.width x.m x.k)) 2 0 3 := by
  apply GeneralPaperSourceSoftBounds.dominated (certificate C d W hW).bound
  intro x
  exact (parameters_mono model (W x) _ _ _ _ _ _ _ _ _ _ le_rfl (hh x) (hR x) le_rfl le_rfl).trans
    (model_mono model (GeneralPaperFastRationalMajorant.model C d) (GeneralPaperFastRationalMajorant.dominates hg) _ _ _ _ _ _)

end Blotto.GeneralPaperSortedConstructionProfileRates
