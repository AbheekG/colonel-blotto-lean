import Blotto.GeneralPaperSourceWorkReferenceScaling

/-! Complete positive reference-word scaling now includes caller work
metadata. Every completed source/column/compiler/pair/value reserve sums
at the same reference; no actual native data or control flow changes. -/
namespace Blotto.GeneralPaperCompleteCallerReferenceScaling
open GeneralPaperReferenceScaling
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 16384

@[fun_prop]
theorem rows_profile (C d m k Qv : ℕ) : Scale
    (fun W => GeneralPaperSourceRowsCallerStorageRates.sourceProfile C d W m k Qv) := by
  have hWork := GeneralPaperSourceWorkReferenceScaling.source_work C d m k Qv
  have hEnvelope := GeneralPaperSourceInputEnvelopeStorage.scaling (GeneralPaperFastRationalMajorant.model C d) m k Qv
    ((GeneralPaperProxyParameters.alphabet m k).lambda+1) (GeneralPaperProxyParameters.alphabet m k) (by omega)
  dsimp only [GeneralPaperSourceRowsCallerStorageRates.sourceProfile,GeneralPaperRetainedSourceRowsCallerStorage.profile,
    GeneralPaperRetainedSourceRowsCallerStorage.metadataCap,GeneralPaperEnclosingSourceOwners.rowsProfile,
    GeneralPaperEncodedBasisStorage.arrayProfile,GeneralPaperEncodedScalarStorage.natBits]
  fun_prop

@[fun_prop]
theorem rows_reservation (model : RationalCostModel) (C d m k Qv : ℕ) : Scale
    (fun W => GeneralPaperSourceRowsCallerStorageRates.reservation model C d W m k Qv) := by
  have hOld := GeneralPaperSourceUnitCallerStorageRates.reservation_scaling model m k Qv
  have hNew := rows_profile C d m k Qv
  unfold GeneralPaperSourceRowsCallerStorageRates.reservation
  fun_prop

@[fun_prop]
theorem unit_price (model : RationalCostModel) (m k : ℕ) : Scale
    (fun W => GeneralPaperSourceColumnCallerStorageRates.unitPrice model W m k) := by
  dsimp only [GeneralPaperSourceCompilerPairStorageRates.sourceProfile,GeneralPaperSourceCompilerPairStorageRates.endpointPrice,GeneralPaperRetainedCompilerPairStorage.profile,
    GeneralPaperRetainedCompilerPairStorage.pairProfile,GeneralPaperRetainedCompilerPairStorage.price,GeneralPaperRetainedCompilerPairStorage.metadataCap,
    GeneralPaperSourceModifiedColumnStorageRates.price,GeneralPaperSourceEndpointFractionConstructionStorageRates.operandWidth,GeneralPaperClassifierResultStorage.profile,
    GeneralPaperPrecallCacheStorage.payload,GeneralPaperSelectionPoints.width,GeneralPaperEncodedBasisStorage.arrayProfile,
    GeneralPaperSourceCompilerBranchStorageRates.price,GeneralPaperSourceUnitCallerStorageRates.operandWidth,GeneralPaperEncodedRationalRows.rowProfile,
    GeneralPaperNativeEndpointColumnsStorage.profile,GeneralPaperRetainedCompilerBranchStorage.price,GeneralPaperRetainedModifiedColumnStorage.metadataCap,
    GeneralPaperSourceCompilerBranchStorageRates.tagPrice,GeneralPaperSourceCompilerBranchStorageRates.testPrice,GeneralPaperSourceOuterEndpointStorageRates.price,
    GeneralPaperSourceStrictPreparationBits.profile,GeneralPaperEnclosingSourceOwners.columnsProfile,GeneralPaperNativeEndpointColumnsStorage.fieldProfile,
    GeneralPaperNativeEndpointColumnsStorage.metadataCap,GeneralPaperRetainedModifiedColumnStorage.price,GeneralPaperRetainedTransferPrice.bitProfile,
    GeneralPaperSourceBasisControllerStorageRates.workPrice,GeneralPaperSourceEndpointContinuationReturnBounds.price,GeneralPaperSourceEndpointScalarStorageRates.operandWidth,
    GeneralPaperSourceInitializerReturnStorageRates.inputPrice,GeneralPaperBasisControllerBits.profile,GeneralPaperEnclosingSourceOwners.columnProfile,
    GeneralPaperNativeEndpointAnchorStorage.profile,GeneralPaperNativeEndpointColumnsStorage.fieldCap,GeneralPaperNativeEndpointColumnsStorage.price,
    GeneralPaperNativePayloadFillStorage.profile,GeneralPaperRawEndpointReturnStorage.price,GeneralPaperRetainedEndpointBitBounds.priceWidth,
    GeneralPaperScoreDPBits.profile,GeneralPaperScoreMatrixBits.matrixProfile,GeneralPaperSourceBasisControllerStorageRates.operandWidth,
    GeneralPaperSourceFinalEndpointReturnRates.affinePrice,GeneralPaperSourceInitializerReturnStorageRates.controlPrice,GeneralPaperSourceInitializerReturnStorageRates.gridPrice,
    GeneralPaperSummaryArrayExecution.arrayWord,GeneralPaperThresholdScanBits.profile,GeneralPaperBasisAffineStorage.price,
    GeneralPaperBasisStepBits.profile,GeneralPaperInitializerControlStorage.price,GeneralPaperNativeEndpointAnchorStorage.scalarCap,
    GeneralPaperNativeEndpointAnchor.width,GeneralPaperNativeEndpointColumnsStorage.fieldPrice,GeneralPaperNativePayloadFillStorage.frameProfile,
    GeneralPaperRawEndpointReturnStorage.evaluationPrice,GeneralPaperScoreDPBits.initialProfile,GeneralPaperScoreDPBits.stepProfile,
    GeneralPaperScoreMatrixBits.fieldProfile,GeneralPaperSourceFinalEndpointReturnRates.operandWidth,GeneralPaperSourceInitializerControlStorageRates.operandWidth,
    GeneralPaperSourceInitializerReturnStorageRates.packedPrice,GeneralPaperSourceInitializerReturnStorageRates.storedPrice,GeneralPaperThresholdScanBits.comparisonWidth,
    GeneralPaperBasisGridPackingPrice.profile,GeneralPaperEncodedScalarStorage.natBits,GeneralPaperEndpointPriceControl.profile,
    GeneralPaperFinalPolytopeStorage.price,GeneralPaperNativeEndpointAnchorStorage.callbackPrice,GeneralPaperNativePayloadFillStorage.metadataCap,
    GeneralPaperScoreBitPrimitive.resourceWidth,GeneralPaperScoreMatrixBits.entryProfile,GeneralPaperSourceBasisGridPackingStorageRates.operandWidth,
    GeneralPaperSourceFinalCheckStorageRates.operandWidth,GeneralPaperSourceInitializerTableStorageRates.operandWidth,GeneralPaperFinalPolytopeBits.profile,
    GeneralPaperHighSearchPriceFacts.profile,GeneralPaperNativePayloadFillStorage.workCap,GeneralPaperScoreMatrixBits.scoreProfile,
    GeneralPaperSourceRawAffineStorageRates.operandWidth,GeneralPaperBoundedQuotient.bitProfile,GeneralPaperFinalRefinementPrice.profile,
    GeneralPaperHighBlockerPrice.profile,GeneralPaperHighSearchPriceControl.profile,GeneralPaperParametricPriceProfiles.profile,
    GeneralPaperScoreArgumentBits.argumentProfile,GeneralPaperStaticScanPrice.profile,GeneralPaperBoundedQuotient.heightBudget,
    GeneralPaperFinalRefinementPrice.envelope,GeneralPaperFixedViolationPrice.profile,GeneralPaperParametricRecursionPrice.profile,
    GeneralPaperParametricStageBits.profile,GeneralPaperScoreArgumentBits.height,GeneralPaperAffineStepPrice.profile,
    GeneralPaperSourceColumnCallerStorageRates.sourceProfile,GeneralPaperSourceColumnCallerStorageRates.unitPrice,GeneralPaperRetainedSourceColumnCallerStorage.profile,
    GeneralPaperRetainedSourceColumnCallerStorage.metadataCap,GeneralPaperRetainedSourceColumnCallerStorage.price,GeneralPaperSourceUnitCallerStorageRates.quantizationPrice,
    GeneralPaperSourceUnitCallerStorageRates.normalizationPrice,GeneralPaperSourceUnitCallerStorageRates.operandCap,GeneralPaperDictionaryNormalizationStorage.price,
    GeneralPaperDivisibleColumnsParentStorage.price,GeneralPaperDictionaryNormalizationStorage.scalePrice,GeneralPaperEnclosingSourceOwners.rowsProfile,
    GeneralPaperQuantizedMatrixParentStorage.price,GeneralPaperDictionaryNormalizationStorage.fieldPrice,GeneralPaperQuantizedMatrixParentStorage.callbackPrice,
    GeneralPaperUnitSourceCallerStorage.price,GeneralPaperQuantizedMatrixParentStorage.fieldPrice,GeneralPaperRationalArrayScaleStorage.price,
    GeneralPaperColumnInputStorage.price,GeneralPaperQuantizedColumnParentStorage.price,GeneralPaperRationalArrayScaleStorage.callbackPrice,
    GeneralPaperQuantizedAnchorStorage.price,GeneralPaperQuantizedLabelScatterStorage.price,GeneralPaperRepresentativeSortStorage.price,
    GeneralPaperNativeIndexedScatterStorage.price,GeneralPaperNativeRepresentativeSort.profile,GeneralPaperQuantizedAnchorStorage.callbackPrice,
    GeneralPaperQuantizedLabelScatterStorage.callbackPrice,GeneralPaperNativeBlockLabelStorage.price,GeneralPaperPricedSort.profile,
    GeneralPaperQuantizedAnchorStorage.operandWord,GeneralPaperNativeBlockLabelStorage.magnitude,GeneralPaperNativeGrowingQuotientStorage.workCap,
    GeneralPaperSourcePreparedPairOwners.price,GeneralPaperSourceCompilerPairStorageRates.price,GeneralPaperRetainedFieldValuesStorage.price,
    GeneralPaperRetainedFieldValuesStorage.callbackPrice,GeneralPaperRetainedFieldValuesStorage.width,GeneralPaperReducedValueArrayPrice.width]
  fun_prop (maxSteps := 4000)

@[fun_prop]
theorem column_profile (model : RationalCostModel) (C d m k Qv : ℕ) : Scale
    (fun W => GeneralPaperSourceColumnCallerStorageRates.sourceProfile model C d W m k Qv) := by
  have hWork := GeneralPaperSourceWorkReferenceScaling.source_work C d m k Qv
  have hUnit := unit_price model m k
  dsimp only [GeneralPaperSourceColumnCallerStorageRates.sourceProfile,GeneralPaperRetainedSourceColumnCallerStorage.profile,
    GeneralPaperRetainedSourceColumnCallerStorage.metadataCap,GeneralPaperRetainedSourceColumnCallerStorage.price,
    GeneralPaperEnclosingSourceOwners.rowsProfile,GeneralPaperEnclosingSourceOwners.columnsProfile,
    GeneralPaperEnclosingSourceOwners.columnProfile,GeneralPaperEncodedBasisStorage.arrayProfile,GeneralPaperEncodedScalarStorage.natBits]
  fun_prop

@[fun_prop]
theorem column_reservation (model : RationalCostModel) (C d m k Qv : ℕ) : Scale
    (fun W => GeneralPaperSourceColumnCallerStorageRates.reservation model C d W m k Qv) := by
  have hOld := rows_reservation model C d m k Qv
  have hNew := column_profile model C d m k Qv
  unfold GeneralPaperSourceColumnCallerStorageRates.reservation
  fun_prop

@[fun_prop]
theorem branch_reservation (model : RationalCostModel) (C d m k Qv : ℕ) : Scale
    (fun W => GeneralPaperSourceCompilerBranchStorageRates.reservation model C d W m k Qv) := by
  have hOld := column_reservation model C d m k Qv
  have hNew := GeneralPaperSourceCompilerBranchStorageRates.source_scaling model m k Qv
  unfold GeneralPaperSourceCompilerBranchStorageRates.reservation
  fun_prop

@[fun_prop]
theorem modified_reservation (model : RationalCostModel) (C d m k Qv : ℕ) : Scale
    (fun W => GeneralPaperSourceModifiedColumnStorageRates.reservation model C d W m k Qv) := by
  have hOld := branch_reservation model C d m k Qv
  have hNew := GeneralPaperSourceModifiedColumnStorageRates.source_scaling model m k Qv
  unfold GeneralPaperSourceModifiedColumnStorageRates.reservation
  fun_prop

@[fun_prop]
theorem pair_reservation (model : RationalCostModel) (C d m k Qv : ℕ) : Scale
    (fun W => GeneralPaperSourceCompilerPairStorageRates.reservation model C d W m k Qv) := by
  have hOld := modified_reservation model C d m k Qv
  have hNew := GeneralPaperSourceCompilerPairStorageRates.source_scaling model m k Qv
  unfold GeneralPaperSourceCompilerPairStorageRates.reservation
  fun_prop

@[fun_prop]
theorem prepared_price (model : RationalCostModel) (C d m k Qv : ℕ) : Scale
    (fun W => GeneralPaperSourcePreparedPairOwners.price model C d W m k Qv) := by
  have hSource := GeneralPaperSourceWorkReferenceScaling.source_work C d m k Qv
  dsimp only [GeneralPaperSourceCompilerPairStorageRates.sourceProfile,GeneralPaperSourceCompilerPairStorageRates.endpointPrice,GeneralPaperRetainedCompilerPairStorage.profile,
    GeneralPaperRetainedCompilerPairStorage.pairProfile,GeneralPaperRetainedCompilerPairStorage.price,GeneralPaperRetainedCompilerPairStorage.metadataCap,
    GeneralPaperSourceModifiedColumnStorageRates.price,GeneralPaperSourceEndpointFractionConstructionStorageRates.operandWidth,GeneralPaperClassifierResultStorage.profile,
    GeneralPaperPrecallCacheStorage.payload,GeneralPaperSelectionPoints.width,GeneralPaperEncodedBasisStorage.arrayProfile,
    GeneralPaperSourceCompilerBranchStorageRates.price,GeneralPaperSourceUnitCallerStorageRates.operandWidth,GeneralPaperEncodedRationalRows.rowProfile,
    GeneralPaperNativeEndpointColumnsStorage.profile,GeneralPaperRetainedCompilerBranchStorage.price,GeneralPaperRetainedModifiedColumnStorage.metadataCap,
    GeneralPaperSourceCompilerBranchStorageRates.tagPrice,GeneralPaperSourceCompilerBranchStorageRates.testPrice,GeneralPaperSourceOuterEndpointStorageRates.price,
    GeneralPaperSourceStrictPreparationBits.profile,GeneralPaperEnclosingSourceOwners.columnsProfile,GeneralPaperNativeEndpointColumnsStorage.fieldProfile,
    GeneralPaperNativeEndpointColumnsStorage.metadataCap,GeneralPaperRetainedModifiedColumnStorage.price,GeneralPaperRetainedTransferPrice.bitProfile,
    GeneralPaperSourceBasisControllerStorageRates.workPrice,GeneralPaperSourceEndpointContinuationReturnBounds.price,GeneralPaperSourceEndpointScalarStorageRates.operandWidth,
    GeneralPaperSourceInitializerReturnStorageRates.inputPrice,GeneralPaperBasisControllerBits.profile,GeneralPaperEnclosingSourceOwners.columnProfile,
    GeneralPaperNativeEndpointAnchorStorage.profile,GeneralPaperNativeEndpointColumnsStorage.fieldCap,GeneralPaperNativeEndpointColumnsStorage.price,
    GeneralPaperNativePayloadFillStorage.profile,GeneralPaperRawEndpointReturnStorage.price,GeneralPaperRetainedEndpointBitBounds.priceWidth,
    GeneralPaperScoreDPBits.profile,GeneralPaperScoreMatrixBits.matrixProfile,GeneralPaperSourceBasisControllerStorageRates.operandWidth,
    GeneralPaperSourceFinalEndpointReturnRates.affinePrice,GeneralPaperSourceInitializerReturnStorageRates.controlPrice,GeneralPaperSourceInitializerReturnStorageRates.gridPrice,
    GeneralPaperSummaryArrayExecution.arrayWord,GeneralPaperThresholdScanBits.profile,GeneralPaperBasisAffineStorage.price,
    GeneralPaperBasisStepBits.profile,GeneralPaperInitializerControlStorage.price,GeneralPaperNativeEndpointAnchorStorage.scalarCap,
    GeneralPaperNativeEndpointAnchor.width,GeneralPaperNativeEndpointColumnsStorage.fieldPrice,GeneralPaperNativePayloadFillStorage.frameProfile,
    GeneralPaperRawEndpointReturnStorage.evaluationPrice,GeneralPaperScoreDPBits.initialProfile,GeneralPaperScoreDPBits.stepProfile,
    GeneralPaperScoreMatrixBits.fieldProfile,GeneralPaperSourceFinalEndpointReturnRates.operandWidth,GeneralPaperSourceInitializerControlStorageRates.operandWidth,
    GeneralPaperSourceInitializerReturnStorageRates.packedPrice,GeneralPaperSourceInitializerReturnStorageRates.storedPrice,GeneralPaperThresholdScanBits.comparisonWidth,
    GeneralPaperBasisGridPackingPrice.profile,GeneralPaperEncodedScalarStorage.natBits,GeneralPaperEndpointPriceControl.profile,
    GeneralPaperFinalPolytopeStorage.price,GeneralPaperNativeEndpointAnchorStorage.callbackPrice,GeneralPaperNativePayloadFillStorage.metadataCap,
    GeneralPaperScoreBitPrimitive.resourceWidth,GeneralPaperScoreMatrixBits.entryProfile,GeneralPaperSourceBasisGridPackingStorageRates.operandWidth,
    GeneralPaperSourceFinalCheckStorageRates.operandWidth,GeneralPaperSourceInitializerTableStorageRates.operandWidth,GeneralPaperFinalPolytopeBits.profile,
    GeneralPaperHighSearchPriceFacts.profile,GeneralPaperNativePayloadFillStorage.workCap,GeneralPaperScoreMatrixBits.scoreProfile,
    GeneralPaperSourceRawAffineStorageRates.operandWidth,GeneralPaperBoundedQuotient.bitProfile,GeneralPaperFinalRefinementPrice.profile,
    GeneralPaperHighBlockerPrice.profile,GeneralPaperHighSearchPriceControl.profile,GeneralPaperParametricPriceProfiles.profile,
    GeneralPaperScoreArgumentBits.argumentProfile,GeneralPaperStaticScanPrice.profile,GeneralPaperBoundedQuotient.heightBudget,
    GeneralPaperFinalRefinementPrice.envelope,GeneralPaperFixedViolationPrice.profile,GeneralPaperParametricRecursionPrice.profile,
    GeneralPaperParametricStageBits.profile,GeneralPaperScoreArgumentBits.height,GeneralPaperAffineStepPrice.profile,
    GeneralPaperSourceColumnCallerStorageRates.sourceProfile,GeneralPaperSourceColumnCallerStorageRates.unitPrice,GeneralPaperRetainedSourceColumnCallerStorage.profile,
    GeneralPaperRetainedSourceColumnCallerStorage.metadataCap,GeneralPaperRetainedSourceColumnCallerStorage.price,GeneralPaperSourceUnitCallerStorageRates.quantizationPrice,
    GeneralPaperSourceUnitCallerStorageRates.normalizationPrice,GeneralPaperSourceUnitCallerStorageRates.operandCap,GeneralPaperDictionaryNormalizationStorage.price,
    GeneralPaperDivisibleColumnsParentStorage.price,GeneralPaperDictionaryNormalizationStorage.scalePrice,GeneralPaperEnclosingSourceOwners.rowsProfile,
    GeneralPaperQuantizedMatrixParentStorage.price,GeneralPaperDictionaryNormalizationStorage.fieldPrice,GeneralPaperQuantizedMatrixParentStorage.callbackPrice,
    GeneralPaperUnitSourceCallerStorage.price,GeneralPaperQuantizedMatrixParentStorage.fieldPrice,GeneralPaperRationalArrayScaleStorage.price,
    GeneralPaperColumnInputStorage.price,GeneralPaperQuantizedColumnParentStorage.price,GeneralPaperRationalArrayScaleStorage.callbackPrice,
    GeneralPaperQuantizedAnchorStorage.price,GeneralPaperQuantizedLabelScatterStorage.price,GeneralPaperRepresentativeSortStorage.price,
    GeneralPaperNativeIndexedScatterStorage.price,GeneralPaperNativeRepresentativeSort.profile,GeneralPaperQuantizedAnchorStorage.callbackPrice,
    GeneralPaperQuantizedLabelScatterStorage.callbackPrice,GeneralPaperNativeBlockLabelStorage.price,GeneralPaperPricedSort.profile,
    GeneralPaperQuantizedAnchorStorage.operandWord,GeneralPaperNativeBlockLabelStorage.magnitude,GeneralPaperNativeGrowingQuotientStorage.workCap,
    GeneralPaperSourcePreparedPairOwners.price,GeneralPaperSourceCompilerPairStorageRates.price,GeneralPaperRetainedFieldValuesStorage.price,
    GeneralPaperRetainedFieldValuesStorage.callbackPrice,GeneralPaperRetainedFieldValuesStorage.width,GeneralPaperReducedValueArrayPrice.width]
  fun_prop (maxSteps := 4000)

@[fun_prop]
theorem prepared_profile (model : RationalCostModel) (C d m k Qv B : ℕ) : Scale
    (fun W => GeneralPaperSourcePreparedPairOwners.profile model C d W m k Qv B) := by
  have hRows := rows_profile C d m k Qv
  have hCols := column_profile model C d m k Qv
  have hPair := GeneralPaperSourceCompilerPairStorageRates.source_scaling model m k Qv
  have hValues := GeneralPaperSourceFieldValuesStorageRates.scaling model m Qv
  have hWork := prepared_price model C d m k Qv
  dsimp only [GeneralPaperSourcePreparedPairOwners.profile,GeneralPaperSourcePreparedPairOwners.metadataCap,
    GeneralPaperEncodedScalarStorage.natBits]
  fun_prop

@[fun_prop]
theorem complete_reservation (model : RationalCostModel) (C d m k Qv B : ℕ) : Scale
    (fun W => GeneralPaperSourcePreparedPairOwnerRates.reservation model C d W m k Qv B) := by
  have hOld := pair_reservation model C d m k Qv
  have hNew := prepared_profile model C d m k Qv B
  unfold GeneralPaperSourcePreparedPairOwnerRates.reservation
  fun_prop

end Blotto.GeneralPaperCompleteCallerReferenceScaling
