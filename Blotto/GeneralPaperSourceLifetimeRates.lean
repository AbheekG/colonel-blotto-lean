import Blotto.GeneralPaperSourceSpacePhaseRates

/-! Rate certificates for actual retained source storage and simultaneous
lifetime profiles. Complete source data remains retained; phase child
payloads use maxima and only caller frames accumulate across recursion. -/
namespace Blotto.GeneralPaperSourceLifetimeRates
open GeneralPaperSourceWordGrowth GeneralPaperSourceSoftBounds GeneralPaperNativeSourceRates
open GeneralPaperSourceRateAlgebra GeneralPaperSourceStorageRates GeneralPaperSourceSpacePhaseRates GeneralPaperInitializerPreparedPoint
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 16384

def lifetimeCertificate (C d : ℕ) (W : Input → ℕ) (hW : Tight W) : Certificate (fun x => GeneralPaperSourceLifetimeStorage.profile (GeneralPaperFastRationalMajorant.model C d) (W x) x.k x.Qv (alphabet x) x.weights (ownBudget x.m x.k (x.b:ℝ) x.reciprocal) (opposingBudget x.m x.k (x.b:ℝ) x.reciprocal)) := by
  have hr : Rated W 0 0 0 := poly (poly_tight W hW)
  have hw : Small W := of_tight hW
  have hwa := weight_array W hW
  have hwas := weight_array_small W hW
  refine ⟨_,_,_,by
    unfold
      GeneralPaperSourceLifetimeStorage.profile
      GeneralPaperSourceLifetimeStorage.phaseProfile
      GeneralPaperSourceLifetimeStorage.returnedProfile
      GeneralPaperSourceLifetimeStorage.appendProfile
      GeneralPaperTrajectoryAppendStorage.profile
      GeneralPaperTrajectoryAppendStorage.rowsProfile
      GeneralPaperTrajectoryAppendStorage.frames
      GeneralPaperEpochSourcePhaseStorage.profile
      GeneralPaperLocalSourceLifetimeStorage.profile
      GeneralPaperTrajectoryControllerStorage.frameProfile
      GeneralPaperLocalSourceLifetimeStorage.phaseProfile
      GeneralPaperLocalSourceLifetimeStorage.returnedProfile
      GeneralPaperLocalSourceLifetimeStorage.baseProfile
      GeneralPaperEpochInitialConstructionStorage.familyProfile
      GeneralPaperEpochInitialConstructionStorage.fieldProfile
      GeneralPaperZeroArrayStorage.profile
      GeneralPaperNativeNatFillStorage.profile
      GeneralPaperEpochSourcePhaseStorage.returnedProfile
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
      GeneralPaperEncodedFixedVector.rankWord
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
      GeneralPaperSourceLifetimeStorage.baseProfile
      GeneralPaperSummaryArrayExecution.arrayWord
      GeneralPaperInitialForestConstructionStorage.profile
      GeneralPaperInitialForestConstructionStorage.returnedProfile
      GeneralPaperInitialForestConstructionStorage.familyProfile
      GeneralPaperInitialForestConstructionStorage.nodeProfile
      GeneralPaperGridArrayConstructionStorage.frames
      GeneralPaperEncodedScalarStorage.natBits
    try dsimp only [GeneralPaperFastRationalMajorant.model]
    try simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil]
    source_space⟩

theorem lifetime_degrees (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    ((lifetimeCertificate C d W hW).fields,(lifetimeCertificate C d W hW).symbols,(lifetimeCertificate C d W hW).accuracy)=(1, 2, 2) := rfl

def residentCertificate  (W : Input → ℕ) (hW : Tight W) : Certificate (fun x => GeneralPaperPrecallResidentStorage.residentProfile (W x) x.k x.Qv (alphabet x) x.weights (ownBudget x.m x.k (x.b:ℝ) x.reciprocal) (opposingBudget x.m x.k (x.b:ℝ) x.reciprocal)) := by
  have hr : Rated W 0 0 0 := poly (poly_tight W hW)
  have hw : Small W := of_tight hW
  have hwa := weight_array W hW
  have hwas := weight_array_small W hW
  refine ⟨_,_,_,by
    unfold
      GeneralPaperPrecallResidentStorage.residentProfile
      GeneralPaperPreparationResidentStorage.residentProfile
      GeneralPaperMaterializedCacheStorage.gridProfile
      GeneralPaperMaterializedCacheStorage.powerProfile
      GeneralPaperPreparationCacheStorage.profile
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
      GeneralPaperEncodedFixedVector.rankWord
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
      GeneralPaperClassifierResultStorage.frontProfile
      GeneralPaperClassifierResultStorage.profile
      GeneralPaperSelectionPoints.width
      GeneralPaperPrecallCacheStorage.payload
    try dsimp only [GeneralPaperFastRationalMajorant.model]
    source_space⟩

def preparationCertificate (C d : ℕ) (W : Input → ℕ) (hW : Tight W) : Certificate (fun x => GeneralPaperPreparationResidentStorage.constructionProfile (GeneralPaperFastRationalMajorant.model C d) (W x) x.m (alphabet x).lambda x.k x.Qv) := by
  have hr : Rated W 0 0 0 := poly (poly_tight W hW)
  have hw : Small W := of_tight hW
  have hwa := weight_array W hW
  have hwas := weight_array_small W hW
  refine ⟨_,_,_,by
    unfold
      GeneralPaperPreparationResidentStorage.constructionProfile
      GeneralPaperPreparationResidentStorage.dyadicProfile
      GeneralPaperPreparationResidentStorage.ceilingProfile
      GeneralPaperPreparationCacheStorage.profile
      GeneralPaperPowerConstructionStorage.profile
      GeneralPaperParameterTemporaryStorage.profile
    try dsimp only [GeneralPaperFastRationalMajorant.model]
    source_space⟩

theorem resident_degrees (W : Input → ℕ) (hW : Tight W) :
    ((residentCertificate W hW).fields,(residentCertificate W hW).symbols,(residentCertificate W hW).accuracy)=(1,2,2) := rfl

theorem preparation_degrees (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    ((preparationCertificate C d W hW).fields,(preparationCertificate C d W hW).symbols,
      (preparationCertificate C d W hW).accuracy)=(0,0,0) := rfl

end Blotto.GeneralPaperSourceLifetimeRates
