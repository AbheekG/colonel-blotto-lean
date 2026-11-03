import Blotto.GeneralPaperSourceRateAlgebra

/-! Checked per-phase source rates. The native price definitions are unfolded,
while balanced DP and short native parameter bounds retain their proved identities.
Different epoch and round powers are kept separate for the final two-term join. -/
namespace Blotto.GeneralPaperNativeSourcePhaseRates
open GeneralPaperSourceWordGrowth GeneralPaperSourceSoftBounds GeneralPaperNativeSourceRates
open GeneralPaperSourceRateAlgebra GeneralPaperFastRationalModel
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 16384

def roundCertificate (C d : ℕ) (W : Input → ℕ) (hW : Tight W) : Certificate (fun x => GeneralPaperSelectorRefinedSourcePrice.roundProfile (GeneralPaperFastRationalMajorant.model C d) C d (W x) x.m (alphabet x).lambda x.k x.Qv) := by
  have hw : Small W := of_tight hW
  have hr : Rated W 0 0 0 := poly (poly_tight W hW)
  refine ⟨_,_,_,by
    unfold
      GeneralPaperSelectorRefinedSourcePrice.roundProfile
      GeneralPaperSelectedRowCodesPrice.profile
      GeneralPaperRoundFieldsPrice.profile
      GeneralPaperFieldUpdateExecution.profile
      GeneralPaperFieldDeltaPrice.uniformProfile
      GeneralPaperDeltaArrayPrice.unsignedProfile
      GeneralPaperUnsignedDeltaStepPrice.profile
      GeneralPaperMeshPairPrice.countsProfile
      GeneralPaperMeshPairPrice.cdfProfile
      GeneralPaperDeltaArrayPrice.signedProfile
      GeneralPaperSignedDeltaStepPrice.profile
      GeneralPaperDecoderControls.operandWidth
      GeneralPaperCachedMeshPrefixQuery.cachedProfile
      GeneralPaperCachedMeshPrefixQuery.profile
      GeneralPaperFieldAdvanceEnvelope.profile
      GeneralPaperEpochLevelPrice.profile
      GeneralPaperBatchCounterPrice.limit
      GeneralPaperFastChooseRowsPrice.profile
      GeneralPaperRoundPrefixViews.profile
      GeneralPaperRoundPrefixViews.familyProfile
      GeneralPaperFastNativeSelectorPrice.pickProfile
      GeneralPaperZeroRowPrice.profile
      GeneralPaperFastNativeSelectorPrice.profile
      GeneralPaperRowTrimPrice.profile
      GeneralPaperRowTrimPrice.word
      GeneralPaperFastRootPrice.profile
      GeneralPaperFastRootPrice.selectionProfile
      GeneralPaperFastRootPrice.rootWord
      GeneralPaperDPTableControls.labelsProfile
      GeneralPaperFastNativeSelectorPrice.preparationProfile
      GeneralPaperProfitTreePreparation.bitProfile
      GeneralPaperTreeHalfPrice.width
      GeneralPaperRankOperands.width
      GeneralPaperNativeProfitFieldsPrice.profile
      GeneralPaperNativeProfitLeafPrice.profile
      GeneralPaperNativeProfitLeafPrice.elementProfile
      GeneralPaperMeshPairPrice.tailsProfile
      GeneralPaperCachedMeshIntervalQuery.cachedProfile
      GeneralPaperCachedMeshIntervalQuery.profile
      GeneralPaperMeshQueryMetadata.referenceWord
      GeneralPaperMeshQueryEnvelope.profile
      GeneralPaperEpochSnapshotFamilyPrice.profile
      GeneralPaperEpochSnapshotPrice.profile
      GeneralPaperEpochSnapshotPrice.blockProfile
      GeneralPaperEpochPrefixPrice.profile
      GeneralPaperEpochNumeratorArrayPrice.profile
      GeneralPaperSummaryArrayExecution.arrayWord
      GeneralPaperEpochNumeratorArrayPrice.elementProfile
    try dsimp only [GeneralPaperFastRationalMajorant.model]
    fun_prop (config := {maxSteps := 20000})⟩

theorem round_degrees (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    ((roundCertificate C d W hW).fields,(roundCertificate C d W hW).symbols,(roundCertificate C d W hW).accuracy)=(1, 1, 2) := rfl

def preparationCertificate (C d : ℕ) (W : Input → ℕ) (hW : Tight W) : Certificate (fun x => GeneralPaperTreeEpochPreparation.profile (GeneralPaperFastRationalMajorant.model C d) (W x) x.m x.k x.Qv (alphabet x)) := by
  have hw : Small W := of_tight hW
  have hr : Rated W 0 0 0 := poly (poly_tight W hW)
  refine ⟨_,_,_,by
    unfold
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
      GeneralPaperDecoderControls.operandWidth
      GeneralPaperCatalogueSlotsPrice.profile
      GeneralPaperCatalogueSlotsPrice.width
      GeneralPaperCachedCatalogueFamily.entriesProfile
      GeneralPaperSummaryArrayExecution.arrayWord
    try dsimp only [GeneralPaperFastRationalMajorant.model]
    fun_prop (config := {maxSteps := 20000})⟩

theorem preparation_degrees (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    ((preparationCertificate C d W hW).fields,(preparationCertificate C d W hW).symbols,(preparationCertificate C d W hW).accuracy)=(1, 2, 1) := rfl

def forestCertificate (C d : ℕ) (W : Input → ℕ) (hW : Tight W) : Certificate (fun x => GeneralPaperForestUpdatePrice.profile (GeneralPaperFastRationalModel.charge (C+1) d) (W x) x.m (alphabet x).lambda x.k x.Qv) := by
  have hw : Small W := of_tight hW
  have hr : Rated W 0 0 0 := poly (poly_tight W hW)
  refine ⟨_,_,_,by
    unfold
      GeneralPaperForestUpdatePrice.profile
      GeneralPaperForestUpdatePrice.familyProfile
      GeneralPaperEpochNodeUpdate.profile
      GeneralPaperCellInstructionPrice.profile
      GeneralPaperSummaryArrayExecution.arrayWord
      GeneralPaperBatchUpdateBitPrice.entryProfile
      GeneralPaperBatchUpdateBitPrice.rootProfile
      GeneralPaperRangeUpdateBitPrice.nodeProfile
      GeneralPaperDecoderControls.operandWidth
      GeneralPaperBatchCounterPrice.limit
    try dsimp only [GeneralPaperFastRationalMajorant.model]
    fun_prop (config := {maxSteps := 20000})⟩

theorem forest_degrees (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    ((forestCertificate C d W hW).fields,(forestCertificate C d W hW).symbols,(forestCertificate C d W hW).accuracy)=(1, 2, 1) := rfl

def localInitialCertificate (C d : ℕ) (W : Input → ℕ) (hW : Tight W) : Certificate (fun x => GeneralPaperEpochInitialFamilyPrice.profile (GeneralPaperFastRationalModel.charge (C+1) d) (W x) x.m x.k) := by
  have hw : Small W := of_tight hW
  have hr : Rated W 0 0 0 := poly (poly_tight W hW)
  refine ⟨_,_,_,by
    unfold
      GeneralPaperEpochInitialFamilyPrice.profile
      GeneralPaperEpochFieldInitialPrice.profile
      GeneralPaperEpochZeroArrayPrice.profile
      GeneralPaperSummaryArrayExecution.arrayWord
      GeneralPaperBatchCounterPrice.limit
    try dsimp only [GeneralPaperFastRationalMajorant.model]
    fun_prop (config := {maxSteps := 20000})⟩

theorem localInitial_degrees (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    ((localInitialCertificate C d W hW).fields,(localInitialCertificate C d W hW).symbols,(localInitialCertificate C d W hW).accuracy)=(1, 0, 1) := rfl

def initialCertificate (_C _d : ℕ) (W : Input → ℕ) (hW : Tight W) : Certificate (fun x => GeneralPaperGeometricSourcePrice.initialProfile (W x) x.m (alphabet x).lambda x.k) := by
  have hw : Small W := of_tight hW
  have hr : Rated W 0 0 0 := poly (poly_tight W hW)
  refine ⟨_,_,_,by
    unfold
      GeneralPaperGeometricSourcePrice.initialProfile
      GeneralPaperForestInitialPrice.profile
      GeneralPaperSummaryArrayExecution.arrayWord
    try dsimp only [GeneralPaperFastRationalMajorant.model]
    fun_prop (config := {maxSteps := 20000})⟩

theorem initial_degrees (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    ((initialCertificate C d W hW).fields,(initialCertificate C d W hW).symbols,(initialCertificate C d W hW).accuracy)=(1, 0, 0) := rfl

def appendCertificate (_C _d : ℕ) (W : Input → ℕ) (hW : Tight W) : Certificate (fun x => GeneralPaperTrajectoryAppendPrice.profile (W x) (GeneralPaperTrajectoryParameters.prepare (alphabet x).lambda x.k).rows (GeneralPaperTrajectoryParameters.prepare (alphabet x).lambda x.k).period) := by
  have hw : Small W := of_tight hW
  have hr : Rated W 0 0 0 := poly (poly_tight W hW)
  refine ⟨_,_,_,by
    unfold
      GeneralPaperTrajectoryAppendPrice.profile
      GeneralPaperSummaryArrayExecution.arrayWord
    try dsimp only [GeneralPaperFastRationalMajorant.model]
    fun_prop (config := {maxSteps := 20000})⟩

theorem append_degrees (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    ((appendCertificate C d W hW).fields,(appendCertificate C d W hW).symbols,(appendCertificate C d W hW).accuracy)=(0, 0, 1) := rfl

end Blotto.GeneralPaperNativeSourcePhaseRates
