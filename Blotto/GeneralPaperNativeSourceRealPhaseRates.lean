import Blotto.GeneralPaperSourceCoreLogBound

/-! Exact degree certificates for every real-RAM source phase. The DP
recurrence uses its checked balanced envelope; every other arithmetic price
is unfolded. Epoch and round rates remain separate until the horizon join. -/
namespace Blotto.GeneralPaperNativeSourceRealPhaseRates
open GeneralPaperSourceWordGrowth GeneralPaperSourceSoftBounds GeneralPaperNativeSourceRates
open GeneralPaperSourceRateAlgebra GeneralPaperSharpDPArithmeticRate
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxRecDepth 16384

def roundCertificate : Certificate (fun x => GeneralPaperRoundPrice.arithmeticProfile x.m (alphabet x).lambda x.k x.Qv (grid x) (GeneralPaperProfitParameters.prepare x.m (alphabet x).lambda x.k x.Qv).grid.depth (GeneralPaperProfitParameters.parameters x.m (alphabet x).lambda x.k x.Qv).height (GeneralPaperProfitParameters.parameters x.m (alphabet x).lambda x.k x.Qv).leafCount) := by
  have hm := GeneralPaperSourceCoreLogBound.measure_square
  have hh := GeneralPaperSourceCoreLogBound.height_square
  have hk := GeneralPaperSourceCoreLogBound.rank_square
  have hd := GeneralPaperSharpDPArithmeticRate.native_rate
  refine ⟨_,_,_,by
    unfold
      GeneralPaperRoundPrice.arithmeticProfile
      GeneralPaperRoundFieldsPrice.arithmeticProfile
      GeneralPaperFieldUpdateExecution.arithmeticProfile
      GeneralPaperFieldDeltaPrice.uniformArithmeticProfile
      GeneralPaperDeltaArrayPrice.unsignedArithmeticProfile
      GeneralPaperUnsignedDeltaStepPrice.arithmeticProfile
      GeneralPaperMeshPairPrice.countsArithmeticProfile
      GeneralPaperMeshPairPrice.cdfArithmeticProfile
      GeneralPaperDeltaArrayPrice.signedArithmeticProfile
      GeneralPaperSignedDeltaStepPrice.arithmeticProfile
      GeneralPaperCachedMeshPrefixQuery.cachedArithmeticProfile
      GeneralPaperCachedMeshPrefixQuery.arithmeticProfile
      GeneralPaperFieldAdvanceEnvelope.arithmeticProfile
      GeneralPaperEpochLevelPrice.arithmeticProfile
      GeneralPaperBatchCounterPrice.limit
      GeneralPaperEpochSnapshotFamilyPrice.arithmeticProfile
      GeneralPaperEpochSnapshotPrice.arithmeticProfile
      GeneralPaperEpochSnapshotPrice.arithmeticBlockProfile
      GeneralPaperEpochPrefixPrice.arithmeticProfile
      GeneralPaperEpochNumeratorArrayPrice.arithmeticProfile
      GeneralPaperEpochNumeratorArrayPrice.arithmeticElementProfile
      GeneralPaperChooseRowsPrice.arithmeticProfile
      GeneralPaperRoundPrefixViews.arithmeticProfile
      GeneralPaperRoundPrefixViews.arithmeticFamilyProfile
      GeneralPaperNativeSelectorPrice.pickArithmeticProfile
      GeneralPaperNativeSelectorPrice.arithmeticProfile
      GeneralPaperOrderedRootPrice.arithmeticProfile
      GeneralPaperNativeSelectorPreparationPrice.arithmeticProfile
      GeneralPaperProfitTreePreparation.arithmeticProfile
      GeneralPaperNativeProfitFieldsPrice.arithmeticProfile
      GeneralPaperNativeProfitLeafPrice.arithmeticProfile
      GeneralPaperNativeProfitLeafPrice.arithmeticElementProfile
      GeneralPaperMeshPairPrice.tailsArithmeticProfile
      GeneralPaperCachedMeshIntervalQuery.cachedArithmeticProfile
      GeneralPaperCachedMeshIntervalQuery.arithmeticProfile
      GeneralPaperMeshQueryEnvelope.arithmeticProfile
    try dsimp only
    fun_prop (config := {maxSteps := 10000})⟩


theorem round_degrees : (roundCertificate.fields,roundCertificate.symbols,roundCertificate.accuracy)=(1, 0, 2) := rfl

def preparationCertificate : Certificate (fun x => GeneralPaperTreeEpochPreparation.arithmeticProfile x.m x.k x.Qv (alphabet x)) := by
  have hm := GeneralPaperSourceCoreLogBound.measure_square
  have hh := GeneralPaperSourceCoreLogBound.height_square
  have hk := GeneralPaperSourceCoreLogBound.rank_square
  have hd := GeneralPaperSharpDPArithmeticRate.native_rate
  refine ⟨_,_,_,by
    unfold
      GeneralPaperTreeEpochPreparation.arithmeticProfile
      GeneralPaperFourSummaryArrays.arithmeticProfile
      GeneralPaperSummaryFamilyPrice.arithmeticProfile
      GeneralPaperSummaryArrayPrice.arithmeticProfile
      GeneralPaperEpochCachePreparation.arithmeticProfile
      GeneralPaperFieldPlanFamily.arithmeticProfile
      GeneralPaperFieldPlanPreparation.arithmeticProfile
      GeneralPaperCellPlanPrice.unsignedArithmeticProfile
      GeneralPaperUnsignedCellPartitionPrice.arithmeticProfile
      GeneralPaperUnsignedCellInputPrice.arithmeticProfile
      GeneralPaperQueryLossPrice.arithmeticProfile
      GeneralPaperCDFPairPrice.arithmeticProfile
      GeneralPaperCellPlanPrice.signedArithmeticProfile
      GeneralPaperSignedUpdatePrice.arithmeticProfile
      GeneralPaperSignedPositionsPrice.arithmeticProfile
      GeneralPaperCDFShiftPrice.arithmeticProfile
      GeneralPaperSignedCellPartitionPrice.arithmeticProfile
      GeneralPaperSignedCellPositionsPrice.arithmeticProfile
      GeneralPaperSignedCellExtrasPrice.arithmeticProfile
      GeneralPaperEpochPartitionPrice.arithmeticProfile
      GeneralPaperEpochPointPrice.arithmeticProfile
      GeneralPaperCellRepresentativePrice.arithmeticProfile
      GeneralPaperCatalogueOptimizerPreparation.arithmeticProfile
      GeneralPaperOptionPlanFamily.arithmeticProfile
      GeneralPaperSignedTailPrice.arithmeticProfile
      GeneralPaperSignedCutPrice.arithmeticProfile
      GeneralPaperRankArrayPrice.arithmeticProfile
      GeneralPaperCatalogueTagFamily.arithmeticProfile
      GeneralPaperCatalogueTagFamily.rowArithmeticProfile
      GeneralPaperCatalogueArraysExecution.arithmeticProfile
      GeneralPaperCatalogueProjection.arithmeticProfile
      GeneralPaperCatalogueProjection.familyArithmeticProfile
      GeneralPaperCatalogueProjection.rowArithmeticProfile
      GeneralPaperCachedCatalogueFamily.entriesArithmeticProfile
      GeneralPaperCachedCatalogueFamily.arithmeticProfile
      GeneralPaperCachedCataloguePrice.arithmeticProfile
      GeneralPaperCataloguePartitionPrice.arithmeticProfile
      GeneralPaperPartitionPrice.arithmeticProfile
      GeneralPaperPartitionAssemblyPrice.arithmeticProfile
      GeneralPaperBoundaryCellPrice.arithmeticProfile
      GeneralPaperNaturalOrderPrice.profile
      GeneralPaperPricedSort.profile
      GeneralPaperCataloguePointPrice.arithmeticProfile
      GeneralPaperCachedCataloguePrice.finishArithmeticProfile
      GeneralPaperCellCataloguePrice.arithmeticProfile
      GeneralPaperCatalogueSlotsPrice.arithmeticProfile
    try dsimp only
    fun_prop (config := {maxSteps := 10000})⟩


theorem preparation_degrees : (preparationCertificate.fields,preparationCertificate.symbols,preparationCertificate.accuracy)=(1, 1, 1) := rfl

def forestCertificate : Certificate (fun x => GeneralPaperForestUpdatePrice.arithmeticProfile x.m (alphabet x).lambda x.k x.Qv) := by
  have hm := GeneralPaperSourceCoreLogBound.measure_square
  have hh := GeneralPaperSourceCoreLogBound.height_square
  have hk := GeneralPaperSourceCoreLogBound.rank_square
  have hd := GeneralPaperSharpDPArithmeticRate.native_rate
  refine ⟨_,_,_,by
    unfold
      GeneralPaperForestUpdatePrice.arithmeticProfile
      GeneralPaperForestUpdatePrice.arithmeticFamilyProfile
      GeneralPaperEpochNodeUpdate.arithmeticProfile
      GeneralPaperCellInstructionPrice.arithmeticProfile
      GeneralPaperBatchUpdateArithmetic.entryProfile
      GeneralPaperRangeUpdateArithmetic.nodeProfile
      GeneralPaperBatchCounterPrice.limit
    try dsimp only
    fun_prop (config := {maxSteps := 10000})⟩


theorem forest_degrees : (forestCertificate.fields,forestCertificate.symbols,forestCertificate.accuracy)=(1, 1, 1) := rfl

def localInitialCertificate : Certificate (fun x => GeneralPaperEpochInitialFamilyPrice.arithmeticProfile x.m x.k) := by
  have hm := GeneralPaperSourceCoreLogBound.measure_square
  have hh := GeneralPaperSourceCoreLogBound.height_square
  have hk := GeneralPaperSourceCoreLogBound.rank_square
  have hd := GeneralPaperSharpDPArithmeticRate.native_rate
  refine ⟨_,_,_,by
    unfold
      GeneralPaperEpochInitialFamilyPrice.arithmeticProfile
      GeneralPaperEpochFieldInitialPrice.arithmeticProfile
      GeneralPaperEpochZeroArrayPrice.arithmeticProfile
      GeneralPaperBatchCounterPrice.limit
    try dsimp only
    fun_prop (config := {maxSteps := 10000})⟩


theorem localInitial_degrees : (localInitialCertificate.fields,localInitialCertificate.symbols,localInitialCertificate.accuracy)=(1, 0, 1) := rfl

def initialCertificate : Certificate (fun x => GeneralPaperForestInitialPrice.arithmeticProfile x.m+256) := by
  have hm := GeneralPaperSourceCoreLogBound.measure_square
  have hh := GeneralPaperSourceCoreLogBound.height_square
  have hk := GeneralPaperSourceCoreLogBound.rank_square
  have hd := GeneralPaperSharpDPArithmeticRate.native_rate
  refine ⟨_,_,_,by
    unfold
      GeneralPaperForestInitialPrice.arithmeticProfile
    try dsimp only
    fun_prop (config := {maxSteps := 10000})⟩


theorem initial_degrees : (initialCertificate.fields,initialCertificate.symbols,initialCertificate.accuracy)=(1, 0, 0) := rfl

def appendCertificate : Certificate (fun x => GeneralPaperTrajectoryAppendPrice.arithmeticProfile (GeneralPaperTrajectoryParameters.prepare (alphabet x).lambda x.k).period) := by
  have hm := GeneralPaperSourceCoreLogBound.measure_square
  have hh := GeneralPaperSourceCoreLogBound.height_square
  have hk := GeneralPaperSourceCoreLogBound.rank_square
  have hd := GeneralPaperSharpDPArithmeticRate.native_rate
  refine ⟨_,_,_,by
    unfold
      GeneralPaperTrajectoryAppendPrice.arithmeticProfile
    try dsimp only
    fun_prop (config := {maxSteps := 10000})⟩


theorem append_degrees : (appendCertificate.fields,appendCertificate.symbols,appendCertificate.accuracy)=(0, 0, 1) := rfl

end Blotto.GeneralPaperNativeSourceRealPhaseRates
