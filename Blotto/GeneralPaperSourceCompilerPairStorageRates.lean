import Blotto.GeneralPaperRetainedCompilerPairStorage

/-! Native compiler-pair parent storage joins both physical sides and
reached child/fraction windows. Its degree (3,0,3) sums with the prior
phase contract to preserve the paper working-space degree (3,0,4). -/
namespace Blotto.GeneralPaperSourceCompilerPairStorageRates
open GeneralPaperSourceWordGrowth GeneralPaperSourceSoftBounds GeneralPaperSourceRateAlgebra
open GeneralPaperConstructedWordGrowth GeneralPaperCompilerReferenceGrowth
set_option autoImplicit false
set_option maxHeartbeats 9000000
set_option maxRecDepth 16384

def endpointPrice (model : RationalCostModel) (W m k : ℕ) : ℕ :=
  64*W+2*model.rat (GeneralPaperSourceEndpointFractionConstructionStorageRates.operandWidth m k)

noncomputable def sourceProfile (model : RationalCostModel) (W m k Qv : ℕ) : ℕ :=
  GeneralPaperRetainedCompilerPairStorage.profile W
    (GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet m k).lambda k).rows m
    (GeneralPaperProxyParameters.prepare m k).K (GeneralPaperSourceUnitCallerStorageRates.operandWidth m k) (binaryWordWidth Qv)
    (GeneralPaperClassifierResultStorage.profile W m k)
    (GeneralPaperSourceEndpointFractionConstructionStorageRates.operandWidth m k)
    (GeneralPaperSourceModifiedColumnStorageRates.sourceProfile model W m k Qv)
    (GeneralPaperSourceEndpointFractionConstructionStorageRates.sourceProfile model W m k)
    (GeneralPaperSourceModifiedColumnStorageRates.price model W m k Qv) (endpointPrice model W m k)

noncomputable def price (model : RationalCostModel) (W m k Qv : ℕ) : ℕ :=
  GeneralPaperRetainedCompilerPairStorage.price W (GeneralPaperSourceModifiedColumnStorageRates.price model W m k Qv) (endpointPrice model W m k)

theorem source_scaling (model : RationalCostModel) (m k Qv : ℕ) : GeneralPaperReferenceScaling.Scale
    (fun W => sourceProfile model W m k Qv) := by
  have hB := GeneralPaperSourceModifiedColumnStorageRates.source_scaling model m k Qv
  have hE := GeneralPaperSourceEndpointFractionConstructionStorageRates.source_scaling model m k
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
    GeneralPaperParametricStageBits.profile,GeneralPaperScoreArgumentBits.height,GeneralPaperAffineStepPrice.profile]
  fun_prop

theorem source_model_mono (actual upper : RationalCostModel) (h : ∀ n,actual.rat n≤upper.rat n) (W m k Qv : ℕ) :
    sourceProfile actual W m k Qv≤sourceProfile upper W m k Qv := by
  have hB := GeneralPaperSourceModifiedColumnStorageRates.source_model_mono actual upper h W m k Qv
  have hE := GeneralPaperSourceEndpointFractionConstructionStorageRates.source_model_mono actual upper h W m k
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
    GeneralPaperParametricStageBits.profile,GeneralPaperScoreArgumentBits.height,GeneralPaperAffineStepPrice.profile]
  gcongr <;> first | exact hB | exact hE | exact h _

def certificate (C d : ℕ) (W : Input → ℕ) (hW : Tight W) : Certificate
    (fun x => sourceProfile (GeneralPaperFastRationalMajorant.model C d) (W x) x.m x.k x.Qv) := by
  have hr : Rated W 0 0 0 := poly (poly_tight W hW)
  have hw := of_tight hW
  have hRows := GeneralPaperSourceStaticConstructionRates.sharp_rows
  have hA := GeneralPaperSourceSharpOperandRates.anchor_height
  have hsA := GeneralPaperScoreStorageRates.anchor_small
  have hH := GeneralPaperBasisStorageRates.determinant_length
  have hCap := GeneralPaperSourceSharpOperandRates.cap_word
  have hPoint := (GeneralPaperSourceModifiedColumnStorageRates.pointCertificate W hW).bound
  have hR := GeneralPaperSourceSharpOperandRates.ray_width
  have hsR := GeneralPaperSourceRayStorageRates.width_small
  have hsGrid : Small (fun x => GeneralPaperSourceRayStorageWidth.gridWord x.m x.k) := by
    apply GeneralPaperSourceWordGrowth.dominated GeneralPaperSourceRayStorageRates.width_small
    intro x
    unfold GeneralPaperSourceRayStorageWidth.width GeneralPaperSourceRayStorageWidth.rootWidth
    omega
  have hGrid : Rated (fun x => GeneralPaperSourceRayStorageWidth.gridWord x.m x.k) 1 0 1 := by
    apply GeneralPaperSourceSoftBounds.dominated GeneralPaperSourceSharpOperandRates.ray_width
    intro x
    unfold GeneralPaperSourceRayStorageWidth.width GeneralPaperSourceRayStorageWidth.rootWidth
    omega
  have hB := (GeneralPaperSourceModifiedColumnStorageRates.certificate C d W hW).bound
  have hE := (GeneralPaperSourceEndpointFractionConstructionStorageRates.certificate C d W hW).bound
  have hMeasure := GeneralPaperSourceEndpointFractionConstructionStorageRates.classifier_measure_sharp
  have hGridWord := GeneralPaperSourceEndpointFractionConstructionStorageRates.grid_word_sharp
  have hsMeasure := GeneralPaperSourceStorageRates.precall_measure_small
  refine ⟨_,_,_,by
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
    GeneralPaperParametricStageBits.profile,GeneralPaperScoreArgumentBits.height,GeneralPaperAffineStepPrice.profile]
    dsimp only [GeneralPaperFastRationalMajorant.model]
    source_space⟩

theorem degrees (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    ((certificate C d W hW).fields,(certificate C d W hW).symbols,(certificate C d W hW).accuracy)=(3,0,3) := rfl

noncomputable def reservation (actual : RationalCostModel) (C d W m k Qv : ℕ) : ℕ :=
  GeneralPaperSourceModifiedColumnStorageRates.reservation actual C d W m k Qv+sourceProfile actual W m k Qv

def reservationCertificate (C d : ℕ) (W : Input → ℕ) (hW : Tight W) : Certificate
    (fun x => reservation (GeneralPaperFastRationalMajorant.model C d) C d (W x) x.m x.k x.Qv) := by
  refine ⟨3,0,4,?_⟩
  exact GeneralPaperSourceRateAlgebra.add _ _ 3 0 4 3 0 4
    (GeneralPaperSourceModifiedColumnStorageRates.reservationCertificate C d W hW).bound
    (weaken (certificate C d W hW).bound (by decide : 3≤3) (by decide : 0≤0) (by decide : 3≤4))

theorem reservation_degrees (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    ((reservationCertificate C d W hW).fields,(reservationCertificate C d W hW).symbols,(reservationCertificate C d W hW).accuracy)=(3,0,4) := rfl

theorem reservation_mono (actual upper : RationalCostModel) (h : ∀ n,actual.rat n≤upper.rat n) (C d W m k Qv : ℕ) :
    reservation actual C d W m k Qv≤reservation upper C d W m k Qv :=
  Nat.add_le_add (GeneralPaperSourceModifiedColumnStorageRates.reservation_mono actual upper h C d W m k Qv)
    (source_model_mono actual upper h W m k Qv)

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

end Blotto.GeneralPaperSourceCompilerPairStorageRates
