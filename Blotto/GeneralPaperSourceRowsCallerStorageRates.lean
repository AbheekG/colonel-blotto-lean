import Blotto.GeneralPaperRetainedSourceRowsCallerStorage

/-! Complete retained source-row caller ownership, including native work
metadata, at the selected sharp alphabet and trajectory lengths. The added
reserve is summed with all previously checked native caller reserves. -/
namespace Blotto.GeneralPaperSourceRowsCallerStorageRates
open GeneralPaperSourceWordGrowth GeneralPaperSourceSoftBounds GeneralPaperSourceRateAlgebra
open GeneralPaperConstructedWordGrowth GeneralPaperCompilerReferenceGrowth GeneralPaperSourceStorageRates
set_option autoImplicit false
set_option maxHeartbeats 7000000
set_option maxRecDepth 16384

def sourceWorkCap (C d W m k Qv : ℕ) : ℕ := GeneralPaperSourceRowsDriver.bitProfile C d W m k Qv
  ((GeneralPaperProxyParameters.alphabet m k).lambda+1) (GeneralPaperProxyParameters.alphabet m k)
noncomputable def sourceProfile (C d W m k Qv : ℕ) : ℕ :=
  GeneralPaperRetainedSourceRowsCallerStorage.profile (GeneralPaperFastRationalMajorant.model C d) W m k Qv
    ((GeneralPaperProxyParameters.alphabet m k).lambda+1) (sourceWorkCap C d W m k Qv) (GeneralPaperProxyParameters.alphabet m k)

theorem sharp_epochs : Rated (fun x => (GeneralPaperTrajectoryParameters.prepare (alphabet x).lambda x.k).epochs) 1 0 2 := by
  have hL := GeneralPaperSourceSharpOperandRates.alphabet_length
  apply GeneralPaperSourceSoftBounds.dominated (g:=fun x : Input => 2*((alphabet x).lambda+2)*2^(35+x.k))
  · change Rated (fun x : Input => 2*((alphabet x).lambda+2)*2^(35+x.k)) 1 0 2
    source_space
  · intro x
    exact (Nat.le_of_lt (GeneralPaperTrajectoryParameters.epochs_upper (alphabet x).lambda x.k)).trans_eq (by ring)

theorem work_cap_small (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    Small (fun x => sourceWorkCap C d (W x) x.m x.k x.Qv) := by
  apply GeneralPaperSourceRowsStorageRates.soft_small (GeneralPaperSourceRowsSharpContract.bit_profile_soft C d W hW)
  unfold GeneralPaperSharpSourceBitRate.sourceRate monomial GeneralPaperNativeSourceRates.fields
    GeneralPaperNativeSourceRates.symbols GeneralPaperNativeSourceRates.accuracy
  fun_prop

def coarseCertificate (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    Certificate (fun x => sourceProfile C d (W x) x.m x.k x.Qv) := by
  have hr : Rated W 0 0 0 := poly (poly_tight W hW)
  have hw := of_tight hW
  have hL := GeneralPaperSourceRateAlgebra.lambda
  have hRows := GeneralPaperSourceStorageRates.rows
  have hEpochs := GeneralPaperSourceStorageRates.epochs
  have hWork := work_cap_small C d W hW
  refine ⟨_,_,_,by
    unfold sourceProfile
      GeneralPaperRetainedSourceRowsCallerStorage.profile GeneralPaperEnclosingSourceOwners.rowsProfile GeneralPaperRetainedSourceRowsCallerStorage.metadataCap
      GeneralPaperSourceInputEnvelopeStorage.inputCap GeneralPaperSourceInputEnvelopeStorage.profile GeneralPaperSourceRowsStorage.profile
      GeneralPaperActualEpochParentStorage.profile GeneralPaperActualProfitTreeStorage.profile GeneralPaperActualUpdateConstructionStorage.roundProfile
      GeneralPaperClassifierConstructionStorage.profile GeneralPaperClassifierResultStorage.frontProfile GeneralPaperDPConstructionStorage.profile
      GeneralPaperEncodedBasisStorage.arrayProfile GeneralPaperEpochResidentStorage.profile GeneralPaperEpochSourcePhaseStorage.childrenProfile
      GeneralPaperEpochSourcePhaseStorage.returnedProfile GeneralPaperLocalSourceLifetimeStorage.baseProfile GeneralPaperLocalSourceLifetimeStorage.returnedProfile
      GeneralPaperMaterializedCacheStorage.gridProfile GeneralPaperNativeProfitLeafStorage.elementProfile GeneralPaperNativeSelectorOutputStorage.profile
      GeneralPaperPrecallResidentStorage.inputProfile GeneralPaperPreparationResidentStorage.constructionProfile GeneralPaperRootProfitPhaseStorage.profile
      GeneralPaperSelectedRowConstructionStorage.profile GeneralPaperSharedSpanPrice.width GeneralPaperSnapshotFamilyConstructionStorage.profile
      GeneralPaperSourceGridCallbackStorage.gridProfile GeneralPaperSourceLifetimeStorage.appendProfile GeneralPaperSourceLifetimeStorage.baseProfile
      GeneralPaperSourceLifetimeStorage.returnedProfile GeneralPaperSourceRowsStorage.codeProfile GeneralPaperSourceRowsStorage.peakProfile
      GeneralPaperTrajectoryControllerStorage.frameProfile GeneralPaperActualUpdateConstructionStorage.fieldProfile GeneralPaperCFOperandPrice.width
      GeneralPaperClassifierResultStorage.profile GeneralPaperDPPhaseStorage.phaseBound GeneralPaperEncodedDPStorage.profile
      GeneralPaperEncodedProfitInput.profile GeneralPaperEncodedSharedParameters.preparedProfitProfile GeneralPaperEpochInitialConstructionStorage.familyProfile
      GeneralPaperFieldPreparationPhaseStorage.profile GeneralPaperForestFamilyConstructionStorage.profile GeneralPaperInitialForestConstructionStorage.profile
      GeneralPaperLocalTrajectoryStorage.profile GeneralPaperMaterializedCacheStorage.powerProfile GeneralPaperNativeProfitLeafPrice.elementProfile
      GeneralPaperNativeProfitScalarStorage.coefficientProfile GeneralPaperNativeProfitScalarStorage.profitProfile GeneralPaperNativeSelectorOutputStorage.rootProfile
      GeneralPaperParameterTemporaryStorage.profile GeneralPaperPowerConstructionStorage.profile GeneralPaperPreparationResidentStorage.ceilingProfile
      GeneralPaperPreparationResidentStorage.dyadicProfile GeneralPaperProfitFieldConstructionStorage.prefixProfile GeneralPaperProfitGridQueryStorage.compact
      GeneralPaperProxyLocationStorage.profile GeneralPaperReadyPreparationPhaseStorage.profile GeneralPaperRootSelectionStorage.profile
      GeneralPaperRoundUpdateStorage.profile GeneralPaperRowTrimStorage.profile GeneralPaperSelectedRowConstructionStorage.elementProfile
      GeneralPaperSelectionConstructionStorage.profile GeneralPaperSnapshotConstructionStorage.fieldProfile GeneralPaperSourceRowsStorage.tailProfile
      GeneralPaperTrajectoryAppendStorage.profile GeneralPaperTreeEpochConstructionStorage.profile GeneralPaperTypedDecodeStorage.profile
      GeneralPaperActualUpdateConstructionStorage.nativeProfile GeneralPaperCachedCatalogueStorage.profile GeneralPaperCatalogueArrayConstructionStorage.profile
      GeneralPaperDPPhaseStorage.leafFixed GeneralPaperDPPhaseStorage.mergeFixed GeneralPaperEncodedDPStorage.traceWord
      GeneralPaperEncodedEpochLevels.profile GeneralPaperEncodedLabelStorage.bufferCoefficient GeneralPaperEncodedPreparedPowers.profile
      GeneralPaperEncodedProfitGrid.profile GeneralPaperEncodedProfitInput.fieldProfile GeneralPaperEncodedRationalRows.tableProfile
      GeneralPaperEncodedSnapshotStorage.profile GeneralPaperEpochCacheConstructionStorage.profile GeneralPaperEpochInitialConstructionStorage.fieldProfile
      GeneralPaperFieldFamilyConstructionStorage.rowProfile GeneralPaperFieldPreparationPhaseStorage.childrenProfile GeneralPaperForestFamilyConstructionStorage.familyProfile
      GeneralPaperFourSummaryConstructionStorage.profile GeneralPaperInitialForestConstructionStorage.familyProfile GeneralPaperInitialForestConstructionStorage.returnedProfile
      GeneralPaperPrecallCacheStorage.payload GeneralPaperPreparationCacheStorage.profile GeneralPaperProfitFieldConstructionStorage.optionCap
      GeneralPaperProxyQuotientPrice.envelope GeneralPaperProxyQuotientPrice.word GeneralPaperQuantileComparison.width
      GeneralPaperRootScanStorage.profile GeneralPaperRowTrimStorage.loopFrames GeneralPaperSelectionPoints.width
      GeneralPaperSnapshotConstructionStorage.blockProfile GeneralPaperSourceRowsStorage.fieldProfile GeneralPaperTrajectoryAppendStorage.frames
      GeneralPaperTrajectoryAppendStorage.rowsProfile GeneralPaperTypedDecodeStorage.frame GeneralPaperCatalogueFamilyStorage.profile
      GeneralPaperCataloguePaddingStorage.profile GeneralPaperCataloguePartitionStorage.profile GeneralPaperCatalogueProjectionStorage.familyProfile
      GeneralPaperCatalogueProjectionStorage.rowProfile GeneralPaperCellPlanConstructionStorage.signedProfile GeneralPaperCellPlanConstructionStorage.unsignedProfile
      GeneralPaperDPControlStorage.frame GeneralPaperDPControlStorage.labelsProfile GeneralPaperDPPhaseStorage.applyFixed
      GeneralPaperEncodedEpochCache.profile GeneralPaperEncodedProfitField.profile GeneralPaperEncodedSnapshotStorage.fieldProfile
      GeneralPaperEpochCachePreparation.profile GeneralPaperEpochNodeConstructionStorage.profile GeneralPaperEpochNumeratorConstructionStorage.profile
      GeneralPaperEpochPrefixConstructionStorage.shortProfile GeneralPaperFieldFamilyConstructionStorage.profile GeneralPaperFieldUpdateConstructionStorage.advanceProfile
      GeneralPaperFieldUpdateConstructionStorage.deltaProfile GeneralPaperFourSummaryConstructionStorage.controlWord GeneralPaperFourSummaryConstructionStorage.returnedProfile
      GeneralPaperInitialForestConstructionStorage.nodeProfile GeneralPaperRawCatalogueConstructionStorage.profile GeneralPaperReadyConstructionStorage.profile
      GeneralPaperRowBudgetStorage.profile GeneralPaperSourceRowsStorage.rowPeakProfile GeneralPaperSummaryConstructionStorage.profile
      GeneralPaperSummaryFamilyStorage.familyProfile GeneralPaperZeroArrayStorage.profile GeneralPaperBatchTraversalStorage.frameProfile
      GeneralPaperCachedCatalogueStorage.recordProfile GeneralPaperCatalogueOptimizerPreparation.profile GeneralPaperCataloguePointStorage.profile
      GeneralPaperCatalogueProjectionStorage.rowCapacity GeneralPaperCellPartitionConstructionStorage.signedProfile GeneralPaperCellPartitionConstructionStorage.unsignedProfile
      GeneralPaperDeltaArrayStorage.signedProfile GeneralPaperDeltaArrayStorage.unsignedProfile GeneralPaperEncodedEpochLevels.fieldProfile
      GeneralPaperEncodedFieldPlanStorage.profile GeneralPaperEncodedOptimizerCache.profile GeneralPaperEncodedSnapshotStorage.blockProfile
      GeneralPaperEpochNodeConstructionStorage.instructionProfile GeneralPaperEpochNodeUpdate.profile GeneralPaperEpochNumeratorConstructionStorage.elementProfile
      GeneralPaperFieldPlanFamily.profile GeneralPaperForestConstructorOperands.nodeProfile GeneralPaperFourSummaryConstructionStorage.returnedFamilyProfile
      GeneralPaperLeastValidStorage.cellProfile GeneralPaperLevelArrayStorage.profile GeneralPaperOptionPlanConstructionStorage.profile
      GeneralPaperQuantileQueryStorage.profile GeneralPaperQueryLossConstructionStorage.profile GeneralPaperRangeQueryStorage.profile
      GeneralPaperRankCutArrayStorage.representativeProfile GeneralPaperRawCatalogueConstructionStorage.coefficient GeneralPaperRawCatalogueStorage.entryCapacity
      GeneralPaperRowBudgetStorage.frameProfile GeneralPaperRowBudgetStorage.tailProfile GeneralPaperSignedUpdateConstructionStorage.profile
      GeneralPaperSourceRowsStorage.rowTailProfile GeneralPaperSummaryFamilyStorage.frames GeneralPaperTagFamilyStorage.familyProfile
      GeneralPaperBatchUpdateBitPrice.entryProfile GeneralPaperCDFPairConstructionStorage.profile GeneralPaperCachedPowerQueryStorage.profile
      GeneralPaperCatalogueArraysExecution.profile GeneralPaperCataloguePaddingStorage.entryCapacity GeneralPaperCatalogueTagFamily.profile
      GeneralPaperCellInputConstructionStorage.extrasProfile GeneralPaperCellInputConstructionStorage.positionsProfile GeneralPaperCellInputConstructionStorage.unsignedProfile
      GeneralPaperCellInstructionPrice.profile GeneralPaperClosedBidStorage.profile GeneralPaperDeltaStepStorage.signedProfile
      GeneralPaperDeltaStepStorage.unsignedProfile GeneralPaperEncodedCatalogueStorage.profile GeneralPaperEncodedCellPlans.signedProfile
      GeneralPaperEncodedCellPlans.unsignedProfile GeneralPaperEncodedOptimizerCache.summaryProfile GeneralPaperEncodedOptionCache.profile
      GeneralPaperEncodedRationalRows.rowProfile GeneralPaperEpochNumeratorArrayPrice.elementProfile GeneralPaperEpochPartitionConstructionStorage.profile
      GeneralPaperFieldPlanPreparation.profile GeneralPaperInstructionConstructionStorage.frames GeneralPaperLeastValidStorage.profile
      GeneralPaperLevelArrayStorage.elementProfile GeneralPaperOptionPlanConstructionStorage.rowWindowProfile GeneralPaperOptionPlanFamily.profile
      GeneralPaperPowerPrecision.levelBound GeneralPaperQuantileSearchPrice.profile GeneralPaperQuantileTraversalStorage.coefficient
      GeneralPaperQueryLossConstructionStorage.returnedProfile GeneralPaperRankCutArrayStorage.projectedProfile GeneralPaperRetainedForestNodes.perField
      GeneralPaperRowBudgetExecution.width GeneralPaperSignedUpdateConstructionStorage.returnedProfile GeneralPaperSparseNodeBits.perNode
      GeneralPaperSummaryFamilyStorage.summaryProfile GeneralPaperTagFamilyStorage.rowProfile GeneralPaperBatchCounterPrice.limit
      GeneralPaperBatchUpdateBitPrice.rootProfile GeneralPaperCDFPairConstructionStorage.returnedProfile GeneralPaperCachedCatalogueFamily.entriesProfile
      GeneralPaperCachedCatalogueFamily.profile GeneralPaperCatalogueProjection.profile GeneralPaperCatalogueTagFamily.rowProfile
      GeneralPaperCellPlanPrice.signedProfile GeneralPaperCellPlanPrice.unsignedProfile GeneralPaperClosedBidExecution.width
      GeneralPaperCodeDecodeStorage.profile GeneralPaperEncodedCatalogueStorage.innerProfile GeneralPaperEncodedRankPlans.lossProfile
      GeneralPaperEncodedSignedPlans.profile GeneralPaperEpochPointStorage.profile GeneralPaperIncrementStorage.signedProfile
      GeneralPaperIncrementStorage.unsignedProfile GeneralPaperLeastValidStorage.childProfile GeneralPaperMeshPairStorage.countsProfile
      GeneralPaperOptionPlanConstructionStorage.rowProfile GeneralPaperPartitionConstructionStorage.profile GeneralPaperRankCutArrayStorage.shiftProfile
      GeneralPaperRankRecordConstructionStorage.profile GeneralPaperSignedDeltaStepPrice.profile GeneralPaperSignedTailStorage.profile
      GeneralPaperTagFamilyStorage.rowCapacity GeneralPaperTagValueStorage.profile GeneralPaperUnsignedDeltaStepPrice.profile
      GeneralPaperBoundaryConstructionStorage.profile GeneralPaperCachedCataloguePrice.profile GeneralPaperCatalogueProjection.familyProfile
      GeneralPaperCellRepresentativePrice.profile GeneralPaperCodeScanStorage.profile GeneralPaperCodeSplitStorage.profile
      GeneralPaperEncodedPartitionStorage.profile GeneralPaperEncodedRankPlans.cdfProfile GeneralPaperEncodedRankPlans.tailProfile
      GeneralPaperEncodedScalarStorage.fields GeneralPaperLeastValidStorage.pointProfile GeneralPaperMeshPairPrice.countsProfile
      GeneralPaperMeshPairStorage.cdfProfile GeneralPaperMeshPairStorage.tailsProfile GeneralPaperNaturalOrderConstructionStorage.profile
      GeneralPaperOptionPlanConstructionStorage.tagRowProfile GeneralPaperPartitionConstructionStorage.packingProfile GeneralPaperQueryLossPrice.profile
      GeneralPaperRangeUpdateBitPrice.nodeProfile GeneralPaperRankConstructionStorage.profile GeneralPaperRankCutArrayStorage.coreProfile
      GeneralPaperRankRecordConstructionStorage.recordProfile GeneralPaperSignedCellPartitionPrice.profile GeneralPaperSignedCutStorage.profile
      GeneralPaperSignedTailStorage.rankProfile GeneralPaperSignedTailStorage.returnedProfile GeneralPaperSignedUpdatePrice.profile
      GeneralPaperUnsignedCellPartitionPrice.profile GeneralPaperCDFPairPrice.profile GeneralPaperCachedCataloguePrice.finishProfile
      GeneralPaperCachedMeshQueryStorage.intervalProfile GeneralPaperCachedMeshQueryStorage.prefixProfile GeneralPaperCataloguePartitionPrice.profile
      GeneralPaperCatalogueProjection.rowProfile GeneralPaperCeilingConstructionStorage.word GeneralPaperCodeScanPrice.profile
      GeneralPaperCodeScanStorage.coefficient GeneralPaperCodeScanStorage.evaluateProfile GeneralPaperEncodedRankPlans.base
      GeneralPaperEncodedRankPlans.rankWord GeneralPaperEpochPartitionPrice.profile GeneralPaperMeshPairPrice.cdfProfile
      GeneralPaperMeshPairPrice.tailsProfile GeneralPaperNativeNatFillStorage.profile GeneralPaperNaturalOrderConstructionStorage.sortProfile
      GeneralPaperRankConstructionStorage.frames GeneralPaperRankConstructionStorage.queryProfile GeneralPaperSignedCellExtrasPrice.profile
      GeneralPaperSignedCellPositionsPrice.profile GeneralPaperSignedCutStorage.framePeak GeneralPaperSignedPositionsPrice.profile
      GeneralPaperSignedTailPrice.profile GeneralPaperUnsignedCellInputPrice.profile GeneralPaperCDFShiftPrice.profile
      GeneralPaperCachedMeshIntervalQuery.cachedProfile GeneralPaperCachedMeshPrefixQuery.cachedProfile GeneralPaperCachedMeshQueryStorage.controlWord
      GeneralPaperCataloguePointPrice.profile GeneralPaperCatalogueSlotsPrice.profile GeneralPaperCellCataloguePrice.profile
      GeneralPaperCodeScanPrice.stepProfile GeneralPaperEncodedFixedVector.rankWord GeneralPaperEpochPointPrice.profile
      GeneralPaperGridArrayConstructionStorage.frames GeneralPaperMeshQueryStorage.profile GeneralPaperNaturalOrderConstructionStorage.depth
      GeneralPaperPartitionPrice.profile GeneralPaperRankArrayPrice.profile GeneralPaperSignedCutPrice.profile
      GeneralPaperSignedTailOperands.width GeneralPaperSortConstructionStorage.coefficient GeneralPaperCachedMeshIntervalQuery.profile
      GeneralPaperCachedMeshPrefixQuery.profile GeneralPaperCataloguePointOperands.width GeneralPaperCatalogueSlotsPrice.width
      GeneralPaperCellCataloguePrice.queryProfile GeneralPaperCodeEvaluatePrice.profile GeneralPaperMeshQueryStorage.recordProfile
      GeneralPaperNaturalOrderPrice.profile GeneralPaperPartitionAssemblyPrice.profile GeneralPaperQuotientConstructionStorage.frameCap
      GeneralPaperQuotientConstructionStorage.localCap GeneralPaperRankArrayPrice.queryProfile GeneralPaperRaySearchControls.depth
      GeneralPaperSignedCutOperands.width GeneralPaperSortConstructionStorage.controlWord GeneralPaperBoundaryCellPrice.profile
      GeneralPaperCellCatalogueOperands.width GeneralPaperDecoderControls.controlWord GeneralPaperEncodedScalarStorage.natBits
      GeneralPaperMeshQueryEnvelope.profile GeneralPaperMeshQueryMetadata.referenceWord GeneralPaperPricedSort.profile
      GeneralPaperRankArrayOperands.width GeneralPaperSortConstructionStorage.controlCap GeneralPaperBoundaryCellPrice.width
      GeneralPaperDecoderControls.operandWidth GeneralPaperRankOperands.width GeneralPaperSummaryArrayExecution.arrayWord
    unfold GeneralPaperBoundedQuotient.heightBudget
    dsimp only [GeneralPaperFastRationalMajorant.model]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil]
    source_space⟩

theorem coarse_degrees (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    ((coarseCertificate C d W hW).fields,(coarseCertificate C d W hW).symbols,(coarseCertificate C d W hW).accuracy)=(1,2,2) := rfl

/-- Substitute the checked sharp alphabet rate once, after composing the
coarse source profile, so componentwise maxima do not mix two calibrations. -/
theorem sharpen_source {f : Input → ℕ} (hf : Rated f 1 2 2) : Rated f 3 0 4 := by
  have hL := GeneralPaperSourceSharpOperandRates.alphabet_length
  have hAcc : Rated (fun x : Input => 2^x.k) 0 0 1 := by
    simpa only [Nat.zero_add] using GeneralPaperSourceRateAlgebra.dyadic_accuracy 0
  have hm : Rated (monomial 1 2 2) 3 0 4 := by
    unfold monomial GeneralPaperNativeSourceRates.fields GeneralPaperNativeSourceRates.symbols GeneralPaperNativeSourceRates.accuracy
    source_space
  rcases hf with ⟨A,e,hf⟩
  rcases hm with ⟨B,q,hm⟩
  refine ⟨A*B,q+e,?_⟩
  intro x
  exact (hf x).trans ((Nat.mul_le_mul_right _ (Nat.mul_le_mul_left A (hm x))).trans_eq (by rw [pow_add]; ring))

def certificate (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    Certificate (fun x => sourceProfile C d (W x) x.m x.k x.Qv) :=
  ⟨3,0,4,sharpen_source (coarseCertificate C d W hW).bound⟩

theorem degrees (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    ((certificate C d W hW).fields,(certificate C d W hW).symbols,(certificate C d W hW).accuracy)=(3,0,4) := rfl

noncomputable def reservation (actual : RationalCostModel) (C d W m k Qv : ℕ) : ℕ :=
  GeneralPaperSourceUnitCallerStorageRates.reservation actual W m k Qv+sourceProfile C d W m k Qv

def reservationCertificate (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    Certificate (fun x => reservation (GeneralPaperFastRationalMajorant.model C d) C d (W x) x.m x.k x.Qv) := by
  refine ⟨3,0,4,?_⟩
  exact GeneralPaperSourceRateAlgebra.add _ _ 3 0 4 3 0 4
    (GeneralPaperSourceUnitCallerStorageRates.reservationCertificate C d W hW).bound (certificate C d W hW).bound

theorem reservation_degrees (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    ((reservationCertificate C d W hW).fields,(reservationCertificate C d W hW).symbols,(reservationCertificate C d W hW).accuracy)=(3,0,4) := rfl

theorem reservation_mono (actual upper : RationalCostModel) (h : ∀ n,actual.rat n≤upper.rat n) (C d W m k Qv : ℕ) :
    reservation actual C d W m k Qv≤reservation upper C d W m k Qv :=
  Nat.add_le_add_right (GeneralPaperSourceUnitCallerStorageRates.reservation_mono actual upper h W m k Qv) _

theorem actual_reservation_rate {actual : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth actual C d)
    (W : Input → ℕ) (hW : Tight W) : Rated (fun x => reservation actual C d (W x) x.m x.k x.Qv) 3 0 4 :=
  GeneralPaperSourceSoftBounds.dominated (reservationCertificate C d W hW).bound
    (fun x => reservation_mono actual (GeneralPaperFastRationalMajorant.model C d) (GeneralPaperFastRationalMajorant.dominates hg) C d (W x) x.m x.k x.Qv)

theorem reservation_at_one_small (C d : ℕ) : Small (fun x => reservation (GeneralPaperFastRationalMajorant.model C d) C d 1 x.m x.k x.Qv) := by
  apply GeneralPaperSourceRowsStorageRates.soft_small (reservationCertificate C d (fun _ => 1) (tight_constant 1)).bound
  unfold monomial GeneralPaperNativeSourceRates.fields GeneralPaperNativeSourceRates.symbols GeneralPaperNativeSourceRates.accuracy
  fun_prop

theorem actual_common_word {actual : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth actual C d) :
    ∃ A e : ℕ,∀ x,reservation actual C d (GeneralPaperCompilerReference.width C d x) x.m x.k x.Qv≤A*(x.m+1)^3*2^(4*x.k)*(logSize x)^e := by
  rcases actual_reservation_rate hg (GeneralPaperCompilerReference.width C d) (width_tight C d) with ⟨A,e,hA⟩
  refine ⟨A,e,?_⟩
  intro x
  have he : (GeneralPaperNativeSourceRates.accuracy x)^4=2^(4*x.k) := by simp only [GeneralPaperNativeSourceRates.accuracy,←pow_mul,Nat.mul_comm x.k 4]
  simpa only [monomial,pow_zero,Nat.mul_one,GeneralPaperNativeSourceRates.fields,he,Nat.mul_assoc] using hA x

end Blotto.GeneralPaperSourceRowsCallerStorageRates
