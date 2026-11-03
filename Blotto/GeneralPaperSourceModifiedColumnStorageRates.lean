import Blotto.GeneralPaperSourceModifiedColumnPointBounds

/-! Complete nested endpoint-column materialization and native caller
storage have sharp degree (3,0,3), below the summed paper space (3,0,4). -/
namespace Blotto.GeneralPaperSourceModifiedColumnStorageRates
open GeneralPaperSourceWordGrowth GeneralPaperSourceSoftBounds GeneralPaperSourceRateAlgebra
open GeneralPaperConstructedWordGrowth GeneralPaperCompilerReferenceGrowth
set_option autoImplicit false
set_option maxHeartbeats 7000000
set_option maxRecDepth 16384

noncomputable def sourceProfile (model : RationalCostModel) (W m k Qv : ℕ) : ℕ :=
  GeneralPaperRetainedModifiedColumnStorage.profile model W
    (GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet m k).lambda k).rows m
    (GeneralPaperProxyParameters.prepare m k).K (GeneralPaperSourceUnitCallerStorageRates.operandWidth m k) (binaryWordWidth Qv)
    (GeneralPaperSourceModifiedColumnPointBounds.resultProfile W m k) (GeneralPaperSourceCompilerBranchStorageRates.price model W m k Qv)

def price (model : RationalCostModel) (W m k Qv : ℕ) : ℕ := GeneralPaperRetainedModifiedColumnStorage.price model W m
  (GeneralPaperProxyParameters.prepare m k).K (GeneralPaperSourceCompilerBranchStorageRates.price model W m k Qv)

@[fun_prop]
theorem choice_scaling (m k : ℕ) : GeneralPaperReferenceScaling.Scale
    (fun W => GeneralPaperSourceModifiedColumnPointBounds.resultProfile W m k) := by
  unfold GeneralPaperSourceModifiedColumnPointBounds.resultProfile GeneralPaperSourceModifiedColumnPointBounds.pointProfile
    GeneralPaperSourceEndpointContinuationReturnBounds.pointProfile GeneralPaperRawEndpointReturnStorage.optionProfile GeneralPaperEncodedBasisStorage.arrayProfile
  fun_prop

def pointCertificate (W : Input → ℕ) (hW : Tight W) : Certificate
    (fun x => GeneralPaperSourceModifiedColumnPointBounds.resultProfile (W x) x.m x.k) := by
  have hr : Rated W 0 0 0 := poly (poly_tight W hW)
  have hCap := GeneralPaperSourceSharpOperandRates.cap_word
  have hR := GeneralPaperSourceSharpOperandRates.ray_width
  refine ⟨_,_,_,by
    unfold GeneralPaperSourceModifiedColumnPointBounds.resultProfile GeneralPaperSourceModifiedColumnPointBounds.pointProfile
      GeneralPaperSourceModifiedColumnPointBounds.gammaWidth GeneralPaperSourceEndpointContinuationReturnBounds.pointProfile GeneralPaperRawEndpointReturnStorage.optionProfile
      GeneralPaperEncodedBasisStorage.arrayProfile GeneralPaperSourceEndpointScalarStorageRates.operandWidth GeneralPaperRetainedEndpointBitBounds.priceWidth
      GeneralPaperSourceFinalEndpointReturnRates.operandWidth GeneralPaperSourceFinalCheckStorageRates.operandWidth GeneralPaperSourceRawAffineStorageRates.operandWidth
    source_space⟩

theorem point_degrees (W : Input → ℕ) (hW : Tight W) :
    ((pointCertificate W hW).fields,(pointCertificate W hW).symbols,(pointCertificate W hW).accuracy)=(2,0,2) := rfl

theorem source_scaling (model : RationalCostModel) (m k Qv : ℕ) : GeneralPaperReferenceScaling.Scale (fun W => sourceProfile model W m k Qv) := by
  dsimp only [GeneralPaperSourceModifiedColumnStorageRates.sourceProfile,GeneralPaperRetainedModifiedColumnStorage.profile,GeneralPaperSourceCompilerBranchStorageRates.price,
    GeneralPaperSourceUnitCallerStorageRates.operandWidth,GeneralPaperEncodedRationalRows.rowProfile,GeneralPaperNativeEndpointColumnsStorage.profile,
    GeneralPaperRetainedCompilerBranchStorage.price,GeneralPaperRetainedModifiedColumnStorage.metadataCap,GeneralPaperSourceCompilerBranchStorageRates.tagPrice,
    GeneralPaperSourceCompilerBranchStorageRates.testPrice,GeneralPaperSourceOuterEndpointStorageRates.price,GeneralPaperSourceStrictPreparationBits.profile,
    GeneralPaperEnclosingSourceOwners.columnsProfile,GeneralPaperNativeEndpointColumnsStorage.fieldProfile,GeneralPaperNativeEndpointColumnsStorage.metadataCap,
    GeneralPaperRetainedModifiedColumnStorage.price,GeneralPaperRetainedTransferPrice.bitProfile,GeneralPaperSourceBasisControllerStorageRates.workPrice,
    GeneralPaperSourceEndpointContinuationReturnBounds.price,GeneralPaperSourceEndpointScalarStorageRates.operandWidth,GeneralPaperSourceInitializerReturnStorageRates.inputPrice,
    GeneralPaperBasisControllerBits.profile,GeneralPaperEnclosingSourceOwners.columnProfile,GeneralPaperNativeEndpointAnchorStorage.profile,
    GeneralPaperNativeEndpointColumnsStorage.fieldCap,GeneralPaperNativeEndpointColumnsStorage.price,GeneralPaperNativePayloadFillStorage.profile,
    GeneralPaperRawEndpointReturnStorage.price,GeneralPaperRetainedEndpointBitBounds.priceWidth,GeneralPaperScoreDPBits.profile,
    GeneralPaperScoreMatrixBits.matrixProfile,GeneralPaperSourceBasisControllerStorageRates.operandWidth,GeneralPaperSourceFinalEndpointReturnRates.affinePrice,
    GeneralPaperSourceInitializerReturnStorageRates.controlPrice,GeneralPaperSourceInitializerReturnStorageRates.gridPrice,GeneralPaperSummaryArrayExecution.arrayWord,
    GeneralPaperThresholdScanBits.profile,GeneralPaperBasisAffineStorage.price,GeneralPaperBasisStepBits.profile,
    GeneralPaperEncodedBasisStorage.arrayProfile,GeneralPaperInitializerControlStorage.price,GeneralPaperNativeEndpointAnchorStorage.scalarCap,GeneralPaperNativeEndpointAnchor.width,
    GeneralPaperNativeEndpointColumnsStorage.fieldPrice,GeneralPaperNativePayloadFillStorage.frameProfile,GeneralPaperRawEndpointReturnStorage.evaluationPrice,
    GeneralPaperScoreDPBits.initialProfile,GeneralPaperScoreDPBits.stepProfile,GeneralPaperScoreMatrixBits.fieldProfile,
    GeneralPaperSourceFinalEndpointReturnRates.operandWidth,GeneralPaperSourceInitializerControlStorageRates.operandWidth,GeneralPaperSourceInitializerReturnStorageRates.packedPrice,
    GeneralPaperSourceInitializerReturnStorageRates.storedPrice,GeneralPaperThresholdScanBits.comparisonWidth,GeneralPaperBasisGridPackingPrice.profile,
    GeneralPaperEncodedScalarStorage.natBits,GeneralPaperEndpointPriceControl.profile,GeneralPaperFinalPolytopeStorage.price,
    GeneralPaperNativeEndpointAnchorStorage.callbackPrice,GeneralPaperNativePayloadFillStorage.metadataCap,GeneralPaperScoreBitPrimitive.resourceWidth,
    GeneralPaperScoreMatrixBits.entryProfile,GeneralPaperSourceBasisGridPackingStorageRates.operandWidth,GeneralPaperSourceFinalCheckStorageRates.operandWidth,
    GeneralPaperSourceInitializerTableStorageRates.operandWidth,GeneralPaperFinalPolytopeBits.profile,GeneralPaperHighSearchPriceFacts.profile,
    GeneralPaperNativePayloadFillStorage.workCap,GeneralPaperScoreMatrixBits.scoreProfile,GeneralPaperSourceRawAffineStorageRates.operandWidth,
    GeneralPaperBoundedQuotient.bitProfile,GeneralPaperFinalRefinementPrice.profile,GeneralPaperHighBlockerPrice.profile,
    GeneralPaperHighSearchPriceControl.profile,GeneralPaperParametricPriceProfiles.profile,GeneralPaperScoreArgumentBits.argumentProfile,
    GeneralPaperStaticScanPrice.profile,GeneralPaperBoundedQuotient.heightBudget,GeneralPaperFinalRefinementPrice.envelope,
    GeneralPaperFixedViolationPrice.profile,GeneralPaperParametricRecursionPrice.profile,GeneralPaperParametricStageBits.profile,
    GeneralPaperScoreArgumentBits.height,GeneralPaperAffineStepPrice.profile]
  fun_prop (maxSteps := 4000)

theorem source_model_mono (actual upper : RationalCostModel) (h : ∀ n,actual.rat n≤upper.rat n) (W m k Qv : ℕ) :
    sourceProfile actual W m k Qv≤sourceProfile upper W m k Qv := by
  dsimp only [GeneralPaperSourceModifiedColumnStorageRates.sourceProfile,GeneralPaperRetainedModifiedColumnStorage.profile,GeneralPaperSourceCompilerBranchStorageRates.price,
    GeneralPaperSourceUnitCallerStorageRates.operandWidth,GeneralPaperEncodedRationalRows.rowProfile,GeneralPaperNativeEndpointColumnsStorage.profile,
    GeneralPaperRetainedCompilerBranchStorage.price,GeneralPaperRetainedModifiedColumnStorage.metadataCap,GeneralPaperSourceCompilerBranchStorageRates.tagPrice,
    GeneralPaperSourceCompilerBranchStorageRates.testPrice,GeneralPaperSourceOuterEndpointStorageRates.price,GeneralPaperSourceStrictPreparationBits.profile,
    GeneralPaperEnclosingSourceOwners.columnsProfile,GeneralPaperNativeEndpointColumnsStorage.fieldProfile,GeneralPaperNativeEndpointColumnsStorage.metadataCap,
    GeneralPaperRetainedModifiedColumnStorage.price,GeneralPaperRetainedTransferPrice.bitProfile,GeneralPaperSourceBasisControllerStorageRates.workPrice,
    GeneralPaperSourceEndpointContinuationReturnBounds.price,GeneralPaperSourceEndpointScalarStorageRates.operandWidth,GeneralPaperSourceInitializerReturnStorageRates.inputPrice,
    GeneralPaperBasisControllerBits.profile,GeneralPaperEnclosingSourceOwners.columnProfile,GeneralPaperNativeEndpointAnchorStorage.profile,
    GeneralPaperNativeEndpointColumnsStorage.fieldCap,GeneralPaperNativeEndpointColumnsStorage.price,GeneralPaperNativePayloadFillStorage.profile,
    GeneralPaperRawEndpointReturnStorage.price,GeneralPaperRetainedEndpointBitBounds.priceWidth,GeneralPaperScoreDPBits.profile,
    GeneralPaperScoreMatrixBits.matrixProfile,GeneralPaperSourceBasisControllerStorageRates.operandWidth,GeneralPaperSourceFinalEndpointReturnRates.affinePrice,
    GeneralPaperSourceInitializerReturnStorageRates.controlPrice,GeneralPaperSourceInitializerReturnStorageRates.gridPrice,GeneralPaperSummaryArrayExecution.arrayWord,
    GeneralPaperThresholdScanBits.profile,GeneralPaperBasisAffineStorage.price,GeneralPaperBasisStepBits.profile,
    GeneralPaperEncodedBasisStorage.arrayProfile,GeneralPaperInitializerControlStorage.price,GeneralPaperNativeEndpointAnchorStorage.scalarCap,GeneralPaperNativeEndpointAnchor.width,
    GeneralPaperNativeEndpointColumnsStorage.fieldPrice,GeneralPaperNativePayloadFillStorage.frameProfile,GeneralPaperRawEndpointReturnStorage.evaluationPrice,
    GeneralPaperScoreDPBits.initialProfile,GeneralPaperScoreDPBits.stepProfile,GeneralPaperScoreMatrixBits.fieldProfile,
    GeneralPaperSourceFinalEndpointReturnRates.operandWidth,GeneralPaperSourceInitializerControlStorageRates.operandWidth,GeneralPaperSourceInitializerReturnStorageRates.packedPrice,
    GeneralPaperSourceInitializerReturnStorageRates.storedPrice,GeneralPaperThresholdScanBits.comparisonWidth,GeneralPaperBasisGridPackingPrice.profile,
    GeneralPaperEncodedScalarStorage.natBits,GeneralPaperEndpointPriceControl.profile,GeneralPaperFinalPolytopeStorage.price,
    GeneralPaperNativeEndpointAnchorStorage.callbackPrice,GeneralPaperNativePayloadFillStorage.metadataCap,GeneralPaperScoreBitPrimitive.resourceWidth,
    GeneralPaperScoreMatrixBits.entryProfile,GeneralPaperSourceBasisGridPackingStorageRates.operandWidth,GeneralPaperSourceFinalCheckStorageRates.operandWidth,
    GeneralPaperSourceInitializerTableStorageRates.operandWidth,GeneralPaperFinalPolytopeBits.profile,GeneralPaperHighSearchPriceFacts.profile,
    GeneralPaperNativePayloadFillStorage.workCap,GeneralPaperScoreMatrixBits.scoreProfile,GeneralPaperSourceRawAffineStorageRates.operandWidth,
    GeneralPaperBoundedQuotient.bitProfile,GeneralPaperFinalRefinementPrice.profile,GeneralPaperHighBlockerPrice.profile,
    GeneralPaperHighSearchPriceControl.profile,GeneralPaperParametricPriceProfiles.profile,GeneralPaperScoreArgumentBits.argumentProfile,
    GeneralPaperStaticScanPrice.profile,GeneralPaperBoundedQuotient.heightBudget,GeneralPaperFinalRefinementPrice.envelope,
    GeneralPaperFixedViolationPrice.profile,GeneralPaperParametricRecursionPrice.profile,GeneralPaperParametricStageBits.profile,
    GeneralPaperScoreArgumentBits.height,GeneralPaperAffineStepPrice.profile]
  gcongr <;> exact h _

def certificate (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    Certificate (fun x => sourceProfile (GeneralPaperFastRationalMajorant.model C d) (W x) x.m x.k x.Qv) := by
  have hr : Rated W 0 0 0 := poly (poly_tight W hW)
  have hw := of_tight hW
  have hRows := GeneralPaperSourceStaticConstructionRates.sharp_rows
  have hA := GeneralPaperSourceSharpOperandRates.anchor_height
  have hsA := GeneralPaperScoreStorageRates.anchor_small
  have hH := GeneralPaperBasisStorageRates.determinant_length
  have hCap := GeneralPaperSourceSharpOperandRates.cap_word
  have hB := (pointCertificate W hW).bound
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
  refine ⟨_,_,_,by
    dsimp only [GeneralPaperSourceModifiedColumnStorageRates.sourceProfile,GeneralPaperRetainedModifiedColumnStorage.profile,GeneralPaperSourceCompilerBranchStorageRates.price,
      GeneralPaperSourceUnitCallerStorageRates.operandWidth,GeneralPaperEncodedRationalRows.rowProfile,GeneralPaperNativeEndpointColumnsStorage.profile,
      GeneralPaperRetainedCompilerBranchStorage.price,GeneralPaperRetainedModifiedColumnStorage.metadataCap,GeneralPaperSourceCompilerBranchStorageRates.tagPrice,
      GeneralPaperSourceCompilerBranchStorageRates.testPrice,GeneralPaperSourceOuterEndpointStorageRates.price,GeneralPaperSourceStrictPreparationBits.profile,
      GeneralPaperEnclosingSourceOwners.columnsProfile,GeneralPaperNativeEndpointColumnsStorage.fieldProfile,GeneralPaperNativeEndpointColumnsStorage.metadataCap,
      GeneralPaperRetainedModifiedColumnStorage.price,GeneralPaperRetainedTransferPrice.bitProfile,GeneralPaperSourceBasisControllerStorageRates.workPrice,
      GeneralPaperSourceEndpointContinuationReturnBounds.price,GeneralPaperSourceEndpointScalarStorageRates.operandWidth,GeneralPaperSourceInitializerReturnStorageRates.inputPrice,
      GeneralPaperBasisControllerBits.profile,GeneralPaperEnclosingSourceOwners.columnProfile,GeneralPaperNativeEndpointAnchorStorage.profile,
      GeneralPaperNativeEndpointColumnsStorage.fieldCap,GeneralPaperNativeEndpointColumnsStorage.price,GeneralPaperNativePayloadFillStorage.profile,
      GeneralPaperRawEndpointReturnStorage.price,GeneralPaperRetainedEndpointBitBounds.priceWidth,GeneralPaperScoreDPBits.profile,
      GeneralPaperScoreMatrixBits.matrixProfile,GeneralPaperSourceBasisControllerStorageRates.operandWidth,GeneralPaperSourceFinalEndpointReturnRates.affinePrice,
      GeneralPaperSourceInitializerReturnStorageRates.controlPrice,GeneralPaperSourceInitializerReturnStorageRates.gridPrice,GeneralPaperSummaryArrayExecution.arrayWord,
      GeneralPaperThresholdScanBits.profile,GeneralPaperBasisAffineStorage.price,GeneralPaperBasisStepBits.profile,
      GeneralPaperEncodedBasisStorage.arrayProfile,GeneralPaperInitializerControlStorage.price,GeneralPaperNativeEndpointAnchorStorage.scalarCap,GeneralPaperNativeEndpointAnchor.width,
      GeneralPaperNativeEndpointColumnsStorage.fieldPrice,GeneralPaperNativePayloadFillStorage.frameProfile,GeneralPaperRawEndpointReturnStorage.evaluationPrice,
      GeneralPaperScoreDPBits.initialProfile,GeneralPaperScoreDPBits.stepProfile,GeneralPaperScoreMatrixBits.fieldProfile,
      GeneralPaperSourceFinalEndpointReturnRates.operandWidth,GeneralPaperSourceInitializerControlStorageRates.operandWidth,GeneralPaperSourceInitializerReturnStorageRates.packedPrice,
      GeneralPaperSourceInitializerReturnStorageRates.storedPrice,GeneralPaperThresholdScanBits.comparisonWidth,GeneralPaperBasisGridPackingPrice.profile,
      GeneralPaperEncodedScalarStorage.natBits,GeneralPaperEndpointPriceControl.profile,GeneralPaperFinalPolytopeStorage.price,
      GeneralPaperNativeEndpointAnchorStorage.callbackPrice,GeneralPaperNativePayloadFillStorage.metadataCap,GeneralPaperScoreBitPrimitive.resourceWidth,
      GeneralPaperScoreMatrixBits.entryProfile,GeneralPaperSourceBasisGridPackingStorageRates.operandWidth,GeneralPaperSourceFinalCheckStorageRates.operandWidth,
      GeneralPaperSourceInitializerTableStorageRates.operandWidth,GeneralPaperFinalPolytopeBits.profile,GeneralPaperHighSearchPriceFacts.profile,
      GeneralPaperNativePayloadFillStorage.workCap,GeneralPaperScoreMatrixBits.scoreProfile,GeneralPaperSourceRawAffineStorageRates.operandWidth,
      GeneralPaperBoundedQuotient.bitProfile,GeneralPaperFinalRefinementPrice.profile,GeneralPaperHighBlockerPrice.profile,
      GeneralPaperHighSearchPriceControl.profile,GeneralPaperParametricPriceProfiles.profile,GeneralPaperScoreArgumentBits.argumentProfile,
      GeneralPaperStaticScanPrice.profile,GeneralPaperBoundedQuotient.heightBudget,GeneralPaperFinalRefinementPrice.envelope,
      GeneralPaperFixedViolationPrice.profile,GeneralPaperParametricRecursionPrice.profile,GeneralPaperParametricStageBits.profile,
      GeneralPaperScoreArgumentBits.height,GeneralPaperAffineStepPrice.profile]
    dsimp only [GeneralPaperFastRationalMajorant.model]
    source_space⟩

theorem degrees (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    ((certificate C d W hW).fields,(certificate C d W hW).symbols,(certificate C d W hW).accuracy)=(3,0,3) := rfl

noncomputable def reservation (actual : RationalCostModel) (C d W m k Qv : ℕ) : ℕ :=
  GeneralPaperSourceCompilerBranchStorageRates.reservation actual C d W m k Qv+sourceProfile actual W m k Qv

def reservationCertificate (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    Certificate (fun x => reservation (GeneralPaperFastRationalMajorant.model C d) C d (W x) x.m x.k x.Qv) := by
  refine ⟨3,0,4,?_⟩
  exact GeneralPaperSourceRateAlgebra.add _ _ 3 0 4 3 0 4
    (GeneralPaperSourceCompilerBranchStorageRates.reservationCertificate C d W hW).bound
    (weaken (certificate C d W hW).bound (by decide : 3≤3) (by decide : 0≤0) (by decide : 3≤4))

theorem reservation_degrees (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    ((reservationCertificate C d W hW).fields,(reservationCertificate C d W hW).symbols,(reservationCertificate C d W hW).accuracy)=(3,0,4) := rfl

theorem reservation_mono (actual upper : RationalCostModel) (h : ∀ n,actual.rat n≤upper.rat n) (C d W m k Qv : ℕ) :
    reservation actual C d W m k Qv≤reservation upper C d W m k Qv :=
  Nat.add_le_add (GeneralPaperSourceCompilerBranchStorageRates.reservation_mono actual upper h C d W m k Qv) (source_model_mono actual upper h W m k Qv)

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

end Blotto.GeneralPaperSourceModifiedColumnStorageRates
