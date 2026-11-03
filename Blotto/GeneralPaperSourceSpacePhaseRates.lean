import Blotto.GeneralPaperSourceSpaceTactic

/-! Checked complete native phase storage rates, with retained forests and
trajectories reused as bounds. Only transient phase payloads take maxima;
no runtime, capacity oracle or reconstruction is introduced. -/
namespace Blotto.GeneralPaperSourceSpacePhaseRates
open GeneralPaperSourceWordGrowth GeneralPaperSourceSoftBounds GeneralPaperNativeSourceRates
open GeneralPaperSourceRateAlgebra GeneralPaperSourceStorageRates GeneralPaperInitializerPreparedPoint
set_option autoImplicit false
set_option maxHeartbeats 650000
set_option maxRecDepth 16384

def roundCertificate (C d : ℕ) (W : Input → ℕ) (hW : Tight W) : Certificate (fun x => GeneralPaperRoundPhaseStorage.profile (GeneralPaperFastRationalMajorant.model C d) (W x) x.k x.Qv (alphabet x) x.weights (ownBudget x.m x.k (x.b:ℝ) x.reciprocal) (opposingBudget x.m x.k (x.b:ℝ) x.reciprocal)) := by
  have hr : Rated W 0 0 0 := poly (poly_tight W hW)
  have hw : Small W := of_tight hW
  have hwa := weight_array W hW
  have hwas := weight_array_small W hW
  refine ⟨_,_,_,by
    unfold
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
      GeneralPaperActualRootProfitStorage.profile
      GeneralPaperRootProfitPhaseStorage.profile
      GeneralPaperRootSelectionStorage.profile
      GeneralPaperRootScanStorage.profile
      GeneralPaperProfitFieldConstructionStorage.prefixProfile
      GeneralPaperProfitFieldConstructionStorage.optionCap
      GeneralPaperActualUpdateConstructionStorage.roundProfile
      GeneralPaperRoundUpdateStorage.profile
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
      GeneralPaperQuotientConstructionStorage.localCap
      GeneralPaperQuotientConstructionStorage.frameCap
      GeneralPaperMeshQueryStorage.recordProfile
      GeneralPaperBoundedQuotient.heightBudget
      GeneralPaperCachedMeshQueryStorage.controlWord
      GeneralPaperCachedMeshPrefixQuery.cachedProfile
      GeneralPaperCachedMeshPrefixQuery.profile
      GeneralPaperMeshQueryMetadata.referenceWord
      GeneralPaperMeshQueryEnvelope.profile
      GeneralPaperFieldUpdateConstructionStorage.advanceProfile
      GeneralPaperLevelArrayStorage.profile
      GeneralPaperPowerPrecision.levelBound
      GeneralPaperLevelArrayStorage.elementProfile
      GeneralPaperSelectedRowConstructionStorage.profile
      GeneralPaperSelectedRowConstructionStorage.elementProfile
      GeneralPaperSummaryArrayExecution.arrayWord
      GeneralPaperNativeNatFillStorage.profile
      GeneralPaperGridArrayConstructionStorage.frames
      GeneralPaperActualDPConstructionStorage.profile
      GeneralPaperSelectorResidentStorage.profile
      GeneralPaperNativeSelectorOutputStorage.profile
      GeneralPaperTypedDecodeStorage.profile
      GeneralPaperTypedDecodeStorage.frame
      GeneralPaperEncodedLabelStorage.bufferCoefficient
      GeneralPaperRowTrimStorage.profile
      GeneralPaperRowTrimStorage.loopFrames
      GeneralPaperEncodedScalarStorage.natBits
      GeneralPaperNativeSelectorOutputStorage.rootProfile
      GeneralPaperEpochResidentStorage.profile
      GeneralPaperLocalTrajectoryStorage.profile
      GeneralPaperEncodedSnapshotStorage.profile
      GeneralPaperEncodedSnapshotStorage.fieldProfile
      GeneralPaperEncodedSnapshotStorage.blockProfile
      GeneralPaperEncodedEpochLevels.profile
      GeneralPaperEncodedEpochLevels.fieldProfile
      GeneralPaperEncodedEpochCache.profile
      GeneralPaperEncodedOptimizerCache.profile
      GeneralPaperEncodedOptionCache.profile
      GeneralPaperEncodedOptimizerCache.summaryProfile
      GeneralPaperEncodedCatalogueStorage.profile
      GeneralPaperEncodedCatalogueStorage.innerProfile
      GeneralPaperEncodedFieldPlanStorage.profile
      GeneralPaperEncodedCellPlans.unsignedProfile
      GeneralPaperEncodedRankPlans.lossProfile
      GeneralPaperEncodedRankPlans.tailProfile
      GeneralPaperEncodedRankPlans.cdfProfile
      GeneralPaperEncodedCellPlans.signedProfile
      GeneralPaperEncodedSignedPlans.profile
      GeneralPaperEncodedRankPlans.rankWord
      GeneralPaperEncodedRankPlans.base
      GeneralPaperEncodedPartitionStorage.profile
      GeneralPaperBatchCounterPrice.limit
      GeneralPaperDecoderControls.operandWidth
      GeneralPaperEncodedSharedSource.profile
      GeneralPaperSharedSpanPrice.width
      GeneralPaperEncodedSharedSource.inputFootprint
      GeneralPaperEncodedSharedParameters.preparedProfitProfile
      GeneralPaperEncodedProfitGrid.profile
      GeneralPaperEncodedPreparedPowers.profile
      GeneralPaperActualProfitTreeStorage.profile
      GeneralPaperEncodedProfitInput.profile
      GeneralPaperEncodedProfitInput.fieldProfile
      GeneralPaperEncodedProfitField.profile
      GeneralPaperDPConstructionStorage.profile
      GeneralPaperEncodedDPStorage.profile
      GeneralPaperEncodedDPStorage.traceWord
      GeneralPaperDPPhaseStorage.phaseBound
      GeneralPaperDPPhaseStorage.mergeFixed
      GeneralPaperDPPhaseStorage.leafFixed
      GeneralPaperDPPhaseStorage.applyFixed
      GeneralPaperDPControlStorage.labelsProfile
      GeneralPaperDPControlStorage.frame
      GeneralPaperEncodedFixedVector.rankWord
    try dsimp only [GeneralPaperFastRationalMajorant.model]
    try simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil]
    source_space⟩

@[fun_prop]
theorem round_rate (C d : ℕ) (W : Input → ℕ) (hW : Tight W) : Rated (fun x => GeneralPaperRoundPhaseStorage.profile (GeneralPaperFastRationalMajorant.model C d) (W x) x.k x.Qv (alphabet x) x.weights (ownBudget x.m x.k (x.b:ℝ) x.reciprocal) (opposingBudget x.m x.k (x.b:ℝ) x.reciprocal)) 1 2 2 :=
  weaken (roundCertificate C d W hW).bound (by norm_num [roundCertificate]) (by norm_num [roundCertificate]) (by norm_num [roundCertificate])

def parentsCertificate (C d : ℕ) (W : Input → ℕ) (hW : Tight W) : Certificate (fun x => GeneralPaperActualEpochParentStorage.profile (GeneralPaperFastRationalMajorant.model C d) (W x) x.m x.k x.Qv (alphabet x)) := by
  have hr : Rated W 0 0 0 := poly (poly_tight W hW)
  have hw : Small W := of_tight hW
  have hwa := weight_array W hW
  have hwas := weight_array_small W hW
  refine ⟨_,_,_,by
    unfold
      GeneralPaperActualEpochParentStorage.profile
      GeneralPaperTreeEpochConstructionStorage.profile
      GeneralPaperQuantileComparison.width
      GeneralPaperFourSummaryConstructionStorage.profile
      GeneralPaperSummaryFamilyStorage.familyProfile
      GeneralPaperSummaryFamilyStorage.frames
      GeneralPaperSummaryConstructionStorage.profile
      GeneralPaperQuantileQueryStorage.profile
      GeneralPaperQuantileTraversalStorage.coefficient
      GeneralPaperQuantileSearchPrice.profile
      GeneralPaperFourSummaryConstructionStorage.returnedProfile
      GeneralPaperFourSummaryConstructionStorage.returnedFamilyProfile
      GeneralPaperSummaryFamilyStorage.summaryProfile
      GeneralPaperFourSummaryConstructionStorage.controlWord
      GeneralPaperEpochCacheConstructionStorage.profile
      GeneralPaperReadyConstructionStorage.profile
      GeneralPaperTagFamilyStorage.familyProfile
      GeneralPaperTagFamilyStorage.rowProfile
      GeneralPaperTagValueStorage.profile
      GeneralPaperTagFamilyStorage.rowCapacity
      GeneralPaperOptionPlanConstructionStorage.profile
      GeneralPaperOptionPlanConstructionStorage.rowWindowProfile
      GeneralPaperSignedTailStorage.profile
      GeneralPaperSignedTailStorage.rankProfile
      GeneralPaperSignedCutStorage.profile
      GeneralPaperSignedCutStorage.framePeak
      GeneralPaperRankConstructionStorage.profile
      GeneralPaperRankConstructionStorage.queryProfile
      GeneralPaperRankConstructionStorage.frames
      GeneralPaperOptionPlanConstructionStorage.rowProfile
      GeneralPaperSignedTailStorage.returnedProfile
      GeneralPaperOptionPlanConstructionStorage.tagRowProfile
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
      GeneralPaperSignedTailOperands.width
      GeneralPaperSignedCutPrice.profile
      GeneralPaperSignedCutOperands.width
      GeneralPaperRankArrayPrice.profile
      GeneralPaperRankArrayPrice.queryProfile
      GeneralPaperRankArrayOperands.width
      GeneralPaperRankOperands.width
      GeneralPaperCatalogueTagFamily.profile
      GeneralPaperCatalogueTagFamily.rowProfile
      GeneralPaperCatalogueArraysExecution.profile
      GeneralPaperCatalogueProjection.profile
      GeneralPaperCatalogueProjection.familyProfile
      GeneralPaperCatalogueProjection.rowProfile
      GeneralPaperCachedCatalogueFamily.profile
      GeneralPaperCachedCataloguePrice.profile
      GeneralPaperCataloguePartitionPrice.profile
      GeneralPaperPartitionPrice.profile
      GeneralPaperPartitionAssemblyPrice.profile
      GeneralPaperBoundaryCellPrice.profile
      GeneralPaperBoundaryCellPrice.width
      GeneralPaperNaturalOrderPrice.profile
      GeneralPaperPricedSort.profile
      GeneralPaperCataloguePointPrice.profile
      GeneralPaperCataloguePointOperands.width
      GeneralPaperCachedCataloguePrice.finishProfile
      GeneralPaperCellCataloguePrice.profile
      GeneralPaperCellCataloguePrice.queryProfile
      GeneralPaperDecoderControls.controlWord
      GeneralPaperCellCatalogueOperands.width
      GeneralPaperCatalogueSlotsPrice.profile
      GeneralPaperCatalogueSlotsPrice.width
      GeneralPaperCachedCatalogueFamily.entriesProfile
      GeneralPaperEncodedEpochCache.profile
      GeneralPaperEncodedOptimizerCache.profile
      GeneralPaperEncodedOptionCache.profile
      GeneralPaperEncodedOptimizerCache.summaryProfile
      GeneralPaperEncodedCatalogueStorage.profile
      GeneralPaperEncodedCatalogueStorage.innerProfile
      GeneralPaperEncodedFieldPlanStorage.profile
      GeneralPaperEncodedCellPlans.unsignedProfile
      GeneralPaperEncodedRankPlans.lossProfile
      GeneralPaperEncodedRankPlans.tailProfile
      GeneralPaperEncodedRankPlans.cdfProfile
      GeneralPaperEncodedCellPlans.signedProfile
      GeneralPaperEncodedSignedPlans.profile
      GeneralPaperEncodedRankPlans.rankWord
      GeneralPaperEncodedFixedVector.rankWord
      GeneralPaperEncodedRankPlans.base
      GeneralPaperEncodedPartitionStorage.profile
      GeneralPaperForestFamilyConstructionStorage.profile
      GeneralPaperForestFamilyConstructionStorage.familyProfile
      GeneralPaperGridArrayConstructionStorage.frames
      GeneralPaperEpochNodeConstructionStorage.profile
      GeneralPaperRangeQueryStorage.profile
      GeneralPaperForestConstructorOperands.nodeProfile
      GeneralPaperSparseNodeBits.perNode
      GeneralPaperRetainedForestNodes.perField
      GeneralPaperEpochNodeUpdate.profile
      GeneralPaperCellInstructionPrice.profile
      GeneralPaperSummaryArrayExecution.arrayWord
      GeneralPaperBatchUpdateBitPrice.entryProfile
      GeneralPaperBatchUpdateBitPrice.rootProfile
      GeneralPaperRangeUpdateBitPrice.nodeProfile
      GeneralPaperEpochNodeConstructionStorage.instructionProfile
      GeneralPaperInstructionConstructionStorage.frames
      GeneralPaperBatchTraversalStorage.frameProfile
      GeneralPaperDecoderControls.operandWidth
      GeneralPaperBatchCounterPrice.limit
      GeneralPaperEncodedScalarStorage.fields
      GeneralPaperEncodedScalarStorage.natBits
    try dsimp only [GeneralPaperFastRationalMajorant.model]
    try simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil]
    source_space⟩

@[fun_prop]
theorem parents_rate (C d : ℕ) (W : Input → ℕ) (hW : Tight W) : Rated (fun x => GeneralPaperActualEpochParentStorage.profile (GeneralPaperFastRationalMajorant.model C d) (W x) x.m x.k x.Qv (alphabet x)) 1 2 2 :=
  weaken (parentsCertificate C d W hW).bound (by norm_num [parentsCertificate]) (by norm_num [parentsCertificate]) (by norm_num [parentsCertificate])

def childrenCertificate (C d : ℕ) (W : Input → ℕ) (hW : Tight W) : Certificate (fun x => GeneralPaperEpochSourcePhaseStorage.childrenProfile (GeneralPaperFastRationalMajorant.model C d) (W x) x.m x.k (alphabet x)) := by
  have hr : Rated W 0 0 0 := poly (poly_tight W hW)
  have hw : Small W := of_tight hW
  have hwa := weight_array W hW
  have hwas := weight_array_small W hW
  refine ⟨_,_,_,by
    unfold
      GeneralPaperEpochSourcePhaseStorage.childrenProfile
      GeneralPaperReadyPreparationPhaseStorage.profile
      GeneralPaperReadyConstructionStorage.profile
      GeneralPaperTagFamilyStorage.familyProfile
      GeneralPaperTagFamilyStorage.rowProfile
      GeneralPaperTagValueStorage.profile
      GeneralPaperTagFamilyStorage.rowCapacity
      GeneralPaperOptionPlanConstructionStorage.profile
      GeneralPaperOptionPlanConstructionStorage.rowWindowProfile
      GeneralPaperOptionPlanConstructionStorage.rowProfile
      GeneralPaperOptionPlanConstructionStorage.tagRowProfile
      GeneralPaperEncodedOptimizerCache.profile
      GeneralPaperEncodedOptionCache.profile
      GeneralPaperEncodedOptimizerCache.summaryProfile
      GeneralPaperEncodedCatalogueStorage.profile
      GeneralPaperEncodedCatalogueStorage.innerProfile
      GeneralPaperCatalogueOptimizerPreparation.profile
      GeneralPaperOptionPlanFamily.profile
      GeneralPaperCatalogueTagFamily.profile
      GeneralPaperCatalogueTagFamily.rowProfile
      GeneralPaperCatalogueArrayConstructionStorage.profile
      GeneralPaperCatalogueProjectionStorage.rowProfile
      GeneralPaperCatalogueProjectionStorage.familyProfile
      GeneralPaperCatalogueProjectionStorage.rowCapacity
      GeneralPaperCatalogueFamilyStorage.profile
      GeneralPaperCatalogueArraysExecution.profile
      GeneralPaperCatalogueProjection.profile
      GeneralPaperCatalogueProjection.familyProfile
      GeneralPaperCatalogueProjection.rowProfile
      GeneralPaperCachedCatalogueFamily.profile
      GeneralPaperCachedCatalogueFamily.entriesProfile
      GeneralPaperCachedCatalogueStorage.profile
      GeneralPaperRawCatalogueConstructionStorage.profile
      GeneralPaperRawCatalogueConstructionStorage.coefficient
      GeneralPaperLeastValidStorage.cellProfile
      GeneralPaperLeastValidStorage.profile
      GeneralPaperLeastValidStorage.childProfile
      GeneralPaperLeastValidStorage.pointProfile
      GeneralPaperCodeSplitStorage.profile
      GeneralPaperCodeScanStorage.profile
      GeneralPaperCodeScanStorage.evaluateProfile
      GeneralPaperCodeScanStorage.coefficient
      GeneralPaperCodeScanPrice.profile
      GeneralPaperCodeScanPrice.stepProfile
      GeneralPaperCodeEvaluatePrice.profile
      GeneralPaperCataloguePartitionStorage.profile
      GeneralPaperCataloguePointStorage.profile
      GeneralPaperCataloguePaddingStorage.profile
      GeneralPaperRawCatalogueStorage.entryCapacity
      GeneralPaperCachedCatalogueStorage.recordProfile
      GeneralPaperCataloguePaddingStorage.entryCapacity
      GeneralPaperCachedCataloguePrice.profile
      GeneralPaperCataloguePartitionPrice.profile
      GeneralPaperCataloguePointPrice.profile
      GeneralPaperCachedCataloguePrice.finishProfile
      GeneralPaperCellCataloguePrice.profile
      GeneralPaperCellCataloguePrice.queryProfile
      GeneralPaperDecoderControls.controlWord
      GeneralPaperCellCatalogueOperands.width
      GeneralPaperCatalogueSlotsPrice.profile
      GeneralPaperCatalogueSlotsPrice.width
      GeneralPaperFieldPreparationPhaseStorage.profile
      GeneralPaperFieldPreparationPhaseStorage.childrenProfile
      GeneralPaperCellPlanConstructionStorage.unsignedProfile
      GeneralPaperQueryLossConstructionStorage.profile
      GeneralPaperSignedTailStorage.profile
      GeneralPaperSignedTailStorage.rankProfile
      GeneralPaperSignedCutStorage.profile
      GeneralPaperSignedCutStorage.framePeak
      GeneralPaperQueryLossConstructionStorage.returnedProfile
      GeneralPaperSignedTailStorage.returnedProfile
      GeneralPaperCDFPairConstructionStorage.profile
      GeneralPaperCDFPairConstructionStorage.returnedProfile
      GeneralPaperCellPartitionConstructionStorage.unsignedProfile
      GeneralPaperCellInputConstructionStorage.unsignedProfile
      GeneralPaperCellPlanConstructionStorage.signedProfile
      GeneralPaperSignedUpdateConstructionStorage.profile
      GeneralPaperSignedUpdateConstructionStorage.returnedProfile
      GeneralPaperRankRecordConstructionStorage.profile
      GeneralPaperRankRecordConstructionStorage.recordProfile
      GeneralPaperRankConstructionStorage.profile
      GeneralPaperRankConstructionStorage.queryProfile
      GeneralPaperRankConstructionStorage.frames
      GeneralPaperRankCutArrayStorage.shiftProfile
      GeneralPaperRankCutArrayStorage.projectedProfile
      GeneralPaperRankCutArrayStorage.representativeProfile
      GeneralPaperRankCutArrayStorage.coreProfile
      GeneralPaperCellPartitionConstructionStorage.signedProfile
      GeneralPaperEpochPartitionConstructionStorage.profile
      GeneralPaperPartitionConstructionStorage.profile
      GeneralPaperPartitionConstructionStorage.packingProfile
      GeneralPaperNaturalOrderConstructionStorage.profile
      GeneralPaperNaturalOrderConstructionStorage.sortProfile
      GeneralPaperSortConstructionStorage.coefficient
      GeneralPaperSortConstructionStorage.controlWord
      GeneralPaperSortConstructionStorage.controlCap
      GeneralPaperNaturalOrderConstructionStorage.depth
      GeneralPaperRaySearchControls.depth
      GeneralPaperCeilingConstructionStorage.word
      GeneralPaperBoundaryConstructionStorage.profile
      GeneralPaperEpochPointStorage.profile
      GeneralPaperCellInputConstructionStorage.positionsProfile
      GeneralPaperCellInputConstructionStorage.extrasProfile
      GeneralPaperNativeNatFillStorage.profile
      GeneralPaperFieldFamilyConstructionStorage.rowProfile
      GeneralPaperFieldFamilyConstructionStorage.profile
      GeneralPaperGridArrayConstructionStorage.frames
      GeneralPaperFieldPlanFamily.profile
      GeneralPaperFieldPlanPreparation.profile
      GeneralPaperCellPlanPrice.unsignedProfile
      GeneralPaperUnsignedCellPartitionPrice.profile
      GeneralPaperUnsignedCellInputPrice.profile
      GeneralPaperQueryLossPrice.profile
      GeneralPaperSignedTailPrice.profile
      GeneralPaperSignedCutPrice.profile
      GeneralPaperCDFPairPrice.profile
      GeneralPaperCellPlanPrice.signedProfile
      GeneralPaperSignedUpdatePrice.profile
      GeneralPaperSignedTailOperands.width
      GeneralPaperSignedPositionsPrice.profile
      GeneralPaperRankArrayPrice.profile
      GeneralPaperRankArrayPrice.queryProfile
      GeneralPaperRankArrayOperands.width
      GeneralPaperRankOperands.width
      GeneralPaperCDFShiftPrice.profile
      GeneralPaperSignedCellPartitionPrice.profile
      GeneralPaperSignedCellPositionsPrice.profile
      GeneralPaperSignedCellExtrasPrice.profile
      GeneralPaperEpochPartitionPrice.profile
      GeneralPaperPartitionPrice.profile
      GeneralPaperPartitionAssemblyPrice.profile
      GeneralPaperBoundaryCellPrice.profile
      GeneralPaperBoundaryCellPrice.width
      GeneralPaperNaturalOrderPrice.profile
      GeneralPaperPricedSort.profile
      GeneralPaperEpochPointPrice.profile
      GeneralPaperCataloguePointOperands.width
      GeneralPaperCellRepresentativePrice.profile
      GeneralPaperSummaryArrayExecution.arrayWord
      GeneralPaperSignedCutOperands.width
      GeneralPaperEncodedScalarStorage.fields
      GeneralPaperEncodedScalarStorage.natBits
      GeneralPaperEncodedFieldPlanStorage.profile
      GeneralPaperEncodedCellPlans.unsignedProfile
      GeneralPaperEncodedRankPlans.lossProfile
      GeneralPaperEncodedRankPlans.tailProfile
      GeneralPaperEncodedRankPlans.cdfProfile
      GeneralPaperEncodedCellPlans.signedProfile
      GeneralPaperEncodedSignedPlans.profile
      GeneralPaperEncodedRankPlans.rankWord
      GeneralPaperEncodedFixedVector.rankWord
      GeneralPaperEncodedRankPlans.base
      GeneralPaperEncodedPartitionStorage.profile
      GeneralPaperBatchCounterPrice.limit
      GeneralPaperDecoderControls.operandWidth
    try dsimp only [GeneralPaperFastRationalMajorant.model]
    try simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil]
    source_space⟩

@[fun_prop]
theorem children_rate (C d : ℕ) (W : Input → ℕ) (hW : Tight W) : Rated (fun x => GeneralPaperEpochSourcePhaseStorage.childrenProfile (GeneralPaperFastRationalMajorant.model C d) (W x) x.m x.k (alphabet x)) 1 2 2 :=
  weaken (childrenCertificate C d W hW).bound (by norm_num [childrenCertificate]) (by norm_num [childrenCertificate]) (by norm_num [childrenCertificate])

end Blotto.GeneralPaperSourceSpacePhaseRates
