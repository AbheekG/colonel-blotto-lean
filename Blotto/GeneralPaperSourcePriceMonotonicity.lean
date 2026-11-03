import Blotto.GeneralPaperFastRationalMajorant

/-! Closed source prices are monotone in primitive prices. This theorem
unfolds the checked scalar price definitions, preserves all non-price
parameters, and compares each literal primitive width pointwise. Native
executions and their returned data are not substituted or rerun. -/
namespace Blotto.GeneralPaperSourcePriceMonotonicity
open GeneralPaperCodeAlphabet
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

theorem source (actual upper : RationalCostModel) (hp : ∀ w,actual.rat w≤upper.rat w)
    (C d W m k Qv : ℕ) (a : Alphabet) (count : ℕ) :
    GeneralPaperSelectorRefinedSourcePrice.profile actual C d W m k Qv a count≤
      GeneralPaperSelectorRefinedSourcePrice.profile upper C d W m k Qv a count := by
  unfold
    GeneralPaperSelectorRefinedSourcePrice.profile
    GeneralPaperSelectorRefinedSourcePrice.stepProfile
    GeneralPaperSelectorRefinedSourcePrice.outerProfile
    GeneralPaperTreeEpochPreparation.profile
    GeneralPaperFourSummaryArrays.profile
    GeneralPaperSummaryFamilyPrice.profile
    GeneralPaperSummaryArrayPrice.profile
    GeneralPaperQuantileSearchPrice.profile
    GeneralPaperEpochCachePreparation.profile
    GeneralPaperFieldPlanFamily.profile
    GeneralPaperFieldPlanPreparation.profile
    GeneralPaperCellPlanPrice.unsignedProfile
    GeneralPaperUnsignedCellPartitionPrice.profile
    GeneralPaperUnsignedCellInputPrice.profile
    GeneralPaperQueryLossPrice.profile
    GeneralPaperCDFPairPrice.profile
    GeneralPaperCellPlanPrice.signedProfile
    GeneralPaperSignedUpdatePrice.profile
    GeneralPaperSignedPositionsPrice.profile
    GeneralPaperCDFShiftPrice.profile
    GeneralPaperSignedCellPartitionPrice.profile
    GeneralPaperSignedCellPositionsPrice.profile
    GeneralPaperSignedCellExtrasPrice.profile
    GeneralPaperEpochPartitionPrice.profile
    GeneralPaperEpochPointPrice.profile
    GeneralPaperCellRepresentativePrice.profile
    GeneralPaperCatalogueOptimizerPreparation.profile
    GeneralPaperOptionPlanFamily.profile
    GeneralPaperSignedTailPrice.profile
    GeneralPaperSignedCutPrice.profile
    GeneralPaperRankArrayPrice.profile
    GeneralPaperRankArrayPrice.queryProfile
    GeneralPaperCatalogueTagFamily.profile
    GeneralPaperCatalogueTagFamily.rowProfile
    GeneralPaperCatalogueArraysExecution.profile
    GeneralPaperCachedCatalogueFamily.profile
    GeneralPaperCachedCataloguePrice.profile
    GeneralPaperCataloguePartitionPrice.profile
    GeneralPaperPartitionPrice.profile
    GeneralPaperPartitionAssemblyPrice.profile
    GeneralPaperBoundaryCellPrice.profile
    GeneralPaperCataloguePointPrice.profile
    GeneralPaperCachedCataloguePrice.finishProfile
    GeneralPaperCellCataloguePrice.profile
    GeneralPaperCellCataloguePrice.queryProfile
    GeneralPaperCatalogueSlotsPrice.profile
    GeneralPaperSelectorRefinedSourcePrice.localProfile
    GeneralPaperSelectorRefinedSourcePrice.roundProfile
    GeneralPaperRoundFieldsPrice.profile
    GeneralPaperFieldUpdateExecution.profile
    GeneralPaperFieldDeltaPrice.uniformProfile
    GeneralPaperDeltaArrayPrice.unsignedProfile
    GeneralPaperUnsignedDeltaStepPrice.profile
    GeneralPaperMeshPairPrice.countsProfile
    GeneralPaperMeshPairPrice.tailsProfile
    GeneralPaperCachedMeshIntervalQuery.cachedProfile
    GeneralPaperCachedMeshIntervalQuery.profile
    GeneralPaperMeshPairPrice.cdfProfile
    GeneralPaperDeltaArrayPrice.signedProfile
    GeneralPaperSignedDeltaStepPrice.profile
    GeneralPaperCachedMeshPrefixQuery.cachedProfile
    GeneralPaperCachedMeshPrefixQuery.profile
    GeneralPaperMeshQueryEnvelope.profile
    GeneralPaperFieldAdvanceEnvelope.profile
    GeneralPaperEpochLevelPrice.profile
    GeneralPaperEpochSnapshotFamilyPrice.profile
    GeneralPaperEpochSnapshotPrice.profile
    GeneralPaperEpochSnapshotPrice.blockProfile
    GeneralPaperEpochPrefixPrice.profile
    GeneralPaperEpochNumeratorArrayPrice.profile
    GeneralPaperEpochNumeratorArrayPrice.elementProfile
    GeneralPaperEpochInitialFamilyPrice.profile
    GeneralPaperEpochFieldInitialPrice.profile
    GeneralPaperEpochZeroArrayPrice.profile
    GeneralPaperForestUpdatePrice.profile
    GeneralPaperForestUpdatePrice.familyProfile
    GeneralPaperEpochNodeUpdate.profile
    GeneralPaperBatchUpdateBitPrice.entryProfile
    GeneralPaperBatchUpdateBitPrice.rootProfile
    GeneralPaperRangeUpdateBitPrice.nodeProfile
    GeneralPaperNaturalOrderPrice.profile
    GeneralPaperPricedSort.profile
  dsimp only
  gcongr <;> exact hp _

end Blotto.GeneralPaperSourcePriceMonotonicity
