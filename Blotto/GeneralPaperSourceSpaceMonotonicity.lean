import Blotto.GeneralPaperFastSourceMajorant

/-! Primitive-price monotonicity of the complete closed source/prepared
storage profile. Maxima and finite sums preserve every retained owner and
native lifetime reservation. No runtime space census or replay is used. -/
namespace Blotto.GeneralPaperSourceSpaceMonotonicity
open GeneralPaperCodeAlphabet
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192

theorem prepared {m : ℕ} (actual upper : RationalCostModel) (hp : ∀ w,actual.rat w≤upper.rat w)
    (W k Qv B Hc Hr : ℕ) (a : Alphabet) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) :
    GeneralPaperPreparedReferenceCapacity.profile actual W k Qv B Hc Hr a weights Bc Br≤
      GeneralPaperPreparedReferenceCapacity.profile upper W k Qv B Hc Hr a weights Bc Br := by
  unfold
    GeneralPaperPreparedReferenceCapacity.profile
    GeneralPaperSourceLifetimeStorage.profile
    GeneralPaperSourceLifetimeStorage.phaseProfile
    GeneralPaperEpochSourcePhaseStorage.profile
    GeneralPaperLocalSourceLifetimeStorage.profile
    GeneralPaperLocalSourceLifetimeStorage.phaseProfile
    GeneralPaperRoundPhaseStorage.profile
    GeneralPaperSnapshotFamilyConstructionStorage.profile
    GeneralPaperSnapshotConstructionStorage.fieldProfile
    GeneralPaperSnapshotConstructionStorage.blockProfile
    GeneralPaperEpochPrefixConstructionStorage.shortProfile
    GeneralPaperEpochNumeratorConstructionStorage.profile
    GeneralPaperEpochNumeratorConstructionStorage.elementProfile
    GeneralPaperEpochNumeratorArrayPrice.elementProfile
    GeneralPaperCachedPowerQueryStorage.profile
    GeneralPaperSelectedRowConstructionStorage.sourceProfile
    GeneralPaperSourceUpdateConstructionStorage.profile
    GeneralPaperSourceGridCallbackStorage.profile
    GeneralPaperSourceGridCallbackStorage.gridProfile
    GeneralPaperProfitGridQueryStorage.compact
    GeneralPaperActualQueryCallbackStorage.profile
    GeneralPaperNativeProfitLeafStorage.elementProfile
    GeneralPaperNativeProfitScalarStorage.profitProfile
    GeneralPaperNativeProfitScalarStorage.coefficientProfile
    GeneralPaperNativeProfitLeafPrice.elementProfile
    GeneralPaperActualUpdateConstructionStorage.roundProfile
    GeneralPaperActualUpdateConstructionStorage.fieldProfile
    GeneralPaperActualUpdateConstructionStorage.nativeProfile
    GeneralPaperFieldUpdateConstructionStorage.deltaProfile
    GeneralPaperDeltaArrayStorage.unsignedProfile
    GeneralPaperDeltaStepStorage.unsignedProfile
    GeneralPaperUnsignedDeltaStepPrice.profile
    GeneralPaperMeshPairStorage.countsProfile
    GeneralPaperMeshPairStorage.tailsProfile
    GeneralPaperCachedMeshQueryStorage.intervalProfile
    GeneralPaperMeshPairStorage.cdfProfile
    GeneralPaperMeshPairPrice.countsProfile
    GeneralPaperMeshPairPrice.tailsProfile
    GeneralPaperCachedMeshIntervalQuery.cachedProfile
    GeneralPaperCachedMeshIntervalQuery.profile
    GeneralPaperMeshPairPrice.cdfProfile
    GeneralPaperIncrementStorage.unsignedProfile
    GeneralPaperDeltaArrayStorage.signedProfile
    GeneralPaperDeltaStepStorage.signedProfile
    GeneralPaperSignedDeltaStepPrice.profile
    GeneralPaperIncrementStorage.signedProfile
    GeneralPaperCachedMeshQueryStorage.prefixProfile
    GeneralPaperMeshQueryStorage.profile
    GeneralPaperCachedMeshPrefixQuery.cachedProfile
    GeneralPaperCachedMeshPrefixQuery.profile
    GeneralPaperMeshQueryEnvelope.profile
    GeneralPaperFieldUpdateConstructionStorage.advanceProfile
    GeneralPaperLevelArrayStorage.profile
    GeneralPaperLevelArrayStorage.elementProfile
    GeneralPaperLocalSourceLifetimeStorage.baseProfile
    GeneralPaperEpochInitialConstructionStorage.familyProfile
    GeneralPaperEpochInitialConstructionStorage.fieldProfile
    GeneralPaperZeroArrayStorage.profile
    GeneralPaperEpochSourcePhaseStorage.childrenProfile
    GeneralPaperReadyPreparationPhaseStorage.profile
    GeneralPaperCatalogueArrayConstructionStorage.profile
    GeneralPaperCatalogueFamilyStorage.profile
    GeneralPaperCachedCatalogueStorage.profile
    GeneralPaperRawCatalogueConstructionStorage.profile
    GeneralPaperLeastValidStorage.cellProfile
    GeneralPaperLeastValidStorage.profile
    GeneralPaperLeastValidStorage.childProfile
    GeneralPaperLeastValidStorage.pointProfile
    GeneralPaperCodeSplitStorage.profile
    GeneralPaperCodeScanStorage.profile
    GeneralPaperCodeScanStorage.evaluateProfile
    GeneralPaperCodeScanPrice.profile
    GeneralPaperCodeScanPrice.stepProfile
    GeneralPaperCodeEvaluatePrice.profile
    GeneralPaperCataloguePartitionStorage.profile
    GeneralPaperCataloguePointStorage.profile
    GeneralPaperCataloguePaddingStorage.profile
    GeneralPaperFieldPreparationPhaseStorage.profile
    GeneralPaperFieldPreparationPhaseStorage.childrenProfile
    GeneralPaperCellPlanConstructionStorage.unsignedProfile
    GeneralPaperQueryLossConstructionStorage.profile
    GeneralPaperCDFPairConstructionStorage.profile
    GeneralPaperCellPartitionConstructionStorage.unsignedProfile
    GeneralPaperCellInputConstructionStorage.unsignedProfile
    GeneralPaperCellPlanConstructionStorage.signedProfile
    GeneralPaperSignedUpdateConstructionStorage.profile
    GeneralPaperRankRecordConstructionStorage.profile
    GeneralPaperRankCutArrayStorage.shiftProfile
    GeneralPaperRankCutArrayStorage.projectedProfile
    GeneralPaperRankCutArrayStorage.representativeProfile
    GeneralPaperCellPartitionConstructionStorage.signedProfile
    GeneralPaperEpochPartitionConstructionStorage.profile
    GeneralPaperPartitionConstructionStorage.profile
    GeneralPaperNaturalOrderConstructionStorage.profile
    GeneralPaperNaturalOrderConstructionStorage.sortProfile
    GeneralPaperBoundaryConstructionStorage.profile
    GeneralPaperEpochPointStorage.profile
    GeneralPaperCellInputConstructionStorage.positionsProfile
    GeneralPaperCellInputConstructionStorage.extrasProfile
    GeneralPaperFieldFamilyConstructionStorage.rowProfile
    GeneralPaperActualEpochParentStorage.profile
    GeneralPaperTreeEpochConstructionStorage.profile
    GeneralPaperFourSummaryConstructionStorage.profile
    GeneralPaperSummaryConstructionStorage.profile
    GeneralPaperQuantileQueryStorage.profile
    GeneralPaperQuantileSearchPrice.profile
    GeneralPaperEpochCacheConstructionStorage.profile
    GeneralPaperReadyConstructionStorage.profile
    GeneralPaperTagFamilyStorage.familyProfile
    GeneralPaperTagFamilyStorage.rowProfile
    GeneralPaperTagValueStorage.profile
    GeneralPaperOptionPlanConstructionStorage.profile
    GeneralPaperOptionPlanConstructionStorage.rowWindowProfile
    GeneralPaperSignedTailStorage.profile
    GeneralPaperSignedCutStorage.profile
    GeneralPaperRankConstructionStorage.profile
    GeneralPaperRankConstructionStorage.queryProfile
    GeneralPaperFieldFamilyConstructionStorage.profile
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
    GeneralPaperForestFamilyConstructionStorage.profile
    GeneralPaperForestFamilyConstructionStorage.familyProfile
    GeneralPaperEpochNodeConstructionStorage.profile
    GeneralPaperRangeQueryStorage.profile
    GeneralPaperEpochNodeUpdate.profile
    GeneralPaperBatchUpdateBitPrice.entryProfile
    GeneralPaperBatchUpdateBitPrice.rootProfile
    GeneralPaperRangeUpdateBitPrice.nodeProfile
    GeneralPaperBatchTraversalStorage.frameProfile
    GeneralPaperPreparationResidentStorage.constructionProfile
    GeneralPaperPreparationResidentStorage.dyadicProfile
    GeneralPaperPreparationResidentStorage.ceilingProfile
    GeneralPaperPowerConstructionStorage.profile
    GeneralPaperClassifierConstructionStorage.profile
    GeneralPaperSelectionConstructionStorage.profile
    GeneralPaperProxyLocationStorage.profile
    GeneralPaperQuotientConstructionStorage.localCap
    GeneralPaperNaturalOrderPrice.profile
    GeneralPaperPricedSort.profile
    GeneralPaperSortConstructionStorage.coefficient
  dsimp only
  gcongr <;> exact hp _

end Blotto.GeneralPaperSourceSpaceMonotonicity
