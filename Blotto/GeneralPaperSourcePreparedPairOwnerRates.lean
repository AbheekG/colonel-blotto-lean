import Blotto.GeneralPaperSourcePreparedPairOwners

/-! Complete prepared-pair owners preserve the sharp paper space degree.
Original rational ratio height is additive. All actual source/value/pair
work is encoded only in caller fields, not charged as primitive scratch.
Global reference calibration and remaining outer driver phases stay open. -/
namespace Blotto.GeneralPaperSourcePreparedPairOwnerRates
open GeneralPaperSourceWordGrowth GeneralPaperSourceSoftBounds GeneralPaperSourceRateAlgebra
open GeneralPaperConstructedWordGrowth GeneralPaperCompilerReferenceGrowth
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 16384

theorem price_mono (actual upper : RationalCostModel) (h : ∀ n,actual.rat n≤upper.rat n) (C d W m k Qv : ℕ) :
    GeneralPaperSourcePreparedPairOwners.price actual C d W m k Qv≤GeneralPaperSourcePreparedPairOwners.price upper C d W m k Qv := by
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
  gcongr <;> exact h _

theorem model_mono (actual upper : RationalCostModel) (h : ∀ n,actual.rat n≤upper.rat n) (C d W m k Qv B : ℕ) :
    GeneralPaperSourcePreparedPairOwners.profile actual C d W m k Qv B≤GeneralPaperSourcePreparedPairOwners.profile upper C d W m k Qv B := by
  have hv := GeneralPaperSourceFieldValuesStorageRates.model_mono actual upper h W m Qv
  have hc := GeneralPaperSourceColumnCallerStorageRates.source_model_mono actual upper h C d W m k Qv
  have hp := GeneralPaperSourceCompilerPairStorageRates.source_model_mono actual upper h W m k Qv
  have hw := price_mono actual upper h C d W m k Qv
  unfold GeneralPaperSourcePreparedPairOwners.profile GeneralPaperSourcePreparedPairOwners.metadataCap GeneralPaperEncodedScalarStorage.natBits
  gcongr

@[fun_prop]
theorem price_small (C d : ℕ) (W : Input → ℕ) (hW : Tight W) : Small
    (fun x => GeneralPaperSourcePreparedPairOwners.price (GeneralPaperFastRationalMajorant.model C d) C d (W x) x.m x.k x.Qv) := by
  have hw := of_tight hW
  have hSource := GeneralPaperSourceRowsCallerStorageRates.work_cap_small C d W hW
  have hRay := GeneralPaperSourceRayStorageRates.width_small
  have hGrid : Small (fun x => GeneralPaperSourceRayStorageWidth.gridWord x.m x.k) := by
    apply GeneralPaperSourceWordGrowth.dominated hRay
    intro x
    unfold GeneralPaperSourceRayStorageWidth.width GeneralPaperSourceRayStorageWidth.rootWidth GeneralPaperSourceRayStorageWidth.gridWord
    omega
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
  dsimp only [GeneralPaperFastRationalMajorant.model]
  fun_prop

def certificate (C d : ℕ) (W : Input → ℕ) (hW : Tight W) : Certificate
    (fun x => GeneralPaperSourcePreparedPairOwners.profile (GeneralPaperFastRationalMajorant.model C d) C d (W x) x.m x.k x.Qv 0) := by
  have hr : Rated W 0 0 0 := poly (poly_tight W hW)
  have hw := of_tight hW
  have hRows := (GeneralPaperSourceRowsCallerStorageRates.certificate C d W hW).bound
  have hColumns := (GeneralPaperSourceColumnCallerStorageRates.certificate C d W hW).bound
  have hPair := (GeneralPaperSourceCompilerPairStorageRates.certificate C d W hW).bound
  have hValues := (GeneralPaperSourceFieldValuesStorageRates.certificate C d W hW).bound
  have hPrice := price_small C d W hW
  have hLambda := GeneralPaperSourceSharpOperandRates.alphabet_length
  have hMeasure := GeneralPaperSourceEndpointFractionConstructionStorageRates.classifier_measure_sharp
  have hGridWord := GeneralPaperSourceEndpointFractionConstructionStorageRates.grid_word_sharp
  have hsMeasure := GeneralPaperSourceStorageRates.precall_measure_small
  refine ⟨_,_,_,by
    dsimp only [GeneralPaperSourcePreparedPairOwners.profile,GeneralPaperSourcePreparedPairOwners.metadataCap,
      GeneralPaperEncodedScalarStorage.natBits,GeneralPaperClassifierResultStorage.frontProfile,GeneralPaperClassifierResultStorage.profile,
      GeneralPaperPrecallCacheStorage.payload,GeneralPaperSelectionPoints.width]
    source_space⟩

theorem degrees (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    ((certificate C d W hW).fields,(certificate C d W hW).symbols,(certificate C d W hW).accuracy)=(3,0,4) := rfl

noncomputable def reservation (actual : RationalCostModel) (C d W m k Qv B : ℕ) : ℕ :=
  GeneralPaperSourceCompilerPairStorageRates.reservation actual C d W m k Qv+
    GeneralPaperSourcePreparedPairOwners.profile actual C d W m k Qv B

def reservationCertificate (C d : ℕ) (W : Input → ℕ) (hW : Tight W) : Certificate
    (fun x => reservation (GeneralPaperFastRationalMajorant.model C d) C d (W x) x.m x.k x.Qv 0) := by
  refine ⟨3,0,4,?_⟩
  exact GeneralPaperSourceRateAlgebra.add _ _ 3 0 4 3 0 4
    (GeneralPaperSourceCompilerPairStorageRates.reservationCertificate C d W hW).bound (certificate C d W hW).bound

theorem reservation_degrees (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    ((reservationCertificate C d W hW).fields,(reservationCertificate C d W hW).symbols,(reservationCertificate C d W hW).accuracy)=(3,0,4) := rfl

theorem affine (actual : RationalCostModel) (C d W m k Qv B : ℕ) :
    reservation actual C d W m k Qv B=2*B+reservation actual C d W m k Qv 0 := by
  unfold reservation GeneralPaperSourcePreparedPairOwners.profile
  omega

def rate (x : Input) : ℕ := x.B+1+monomial 3 0 4 x

theorem majorant_rate (C d : ℕ) (W : Input → ℕ) (hW : Tight W) : Soft rate
    (fun x => reservation (GeneralPaperFastRationalMajorant.model C d) C d (W x) x.m x.k x.Qv x.B) := by
  have hRated : Rated (fun x => reservation (GeneralPaperFastRationalMajorant.model C d) C d (W x) x.m x.k x.Qv 0) 3 0 4 :=
    (reservationCertificate C d W hW).bound
  have hBase : Soft rate (fun x => reservation (GeneralPaperFastRationalMajorant.model C d) C d (W x) x.m x.k x.Qv 0) :=
    rate_mono hRated (fun x => by unfold rate;omega)
  have hInput : Soft rate Input.B := rate_mono (identity Input.B) (fun x => by unfold rate;omega)
  have h := add_same (poly_mul_rate (poly_constant 2) hInput) hBase
  apply GeneralPaperSourceSoftBounds.dominated h
  intro x
  rw [affine]

theorem reservation_mono (actual upper : RationalCostModel) (h : ∀ n,actual.rat n≤upper.rat n) (C d W m k Qv B : ℕ) :
    reservation actual C d W m k Qv B≤reservation upper C d W m k Qv B :=
  Nat.add_le_add (GeneralPaperSourceCompilerPairStorageRates.reservation_mono actual upper h C d W m k Qv)
    (model_mono actual upper h C d W m k Qv B)

theorem actual_reservation_rate {actual : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth actual C d)
    (W : Input → ℕ) (hW : Tight W) : Soft rate (fun x => reservation actual C d (W x) x.m x.k x.Qv x.B) :=
  GeneralPaperSourceSoftBounds.dominated (majorant_rate C d W hW)
    (fun x => reservation_mono actual (GeneralPaperFastRationalMajorant.model C d) (GeneralPaperFastRationalMajorant.dominates hg) C d (W x) x.m x.k x.Qv x.B)

theorem reservation_at_one_small (C d : ℕ) : Small
    (fun x => reservation (GeneralPaperFastRationalMajorant.model C d) C d 1 x.m x.k x.Qv x.B) := by
  apply GeneralPaperSourceRowsStorageRates.soft_small (majorant_rate C d (fun _ => 1) (tight_constant 1))
  unfold rate monomial GeneralPaperNativeSourceRates.fields GeneralPaperNativeSourceRates.symbols GeneralPaperNativeSourceRates.accuracy
  fun_prop

theorem actual_common_word {actual : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth actual C d) :
    ∃ A e : ℕ,∀ x,reservation actual C d (GeneralPaperCompilerReference.width C d x) x.m x.k x.Qv x.B≤
      A*(x.B+1+(x.m+1)^3*2^(4*x.k))*(logSize x)^e := by
  obtain ⟨A,e,hA⟩ := actual_reservation_rate hg (GeneralPaperCompilerReference.width C d) (width_tight C d)
  refine ⟨A,e,?_⟩
  intro x
  have he : (GeneralPaperNativeSourceRates.accuracy x)^4=2^(4*x.k) := by simp only [GeneralPaperNativeSourceRates.accuracy,←pow_mul,Nat.mul_comm x.k 4]
  simpa only [rate,monomial,pow_zero,Nat.mul_one,GeneralPaperNativeSourceRates.fields,he,Nat.mul_assoc] using hA x

theorem construction_common_word {model : RationalCostModel} {C d : ℕ}
    (hg : GeneralPaperFastRationalModel.Growth model C d) :
    ∃ A e : ℕ,∀ (x : Input) (_hm : 0<x.m) (hQv : 0<x.Qv) (hp : ∀ j,0<x.weights.read j),
      let W := GeneralPaperCompilerReference.width C d x
      ∀ cursor hc outer ho inner hi,
        GeneralPaperSourcePreparedPairOwners.window model W x.k x.Qv hQv x.weights hp x.weight_sum x.b cursor hc outer ho inner hi≤
          A*(x.B+1+(x.m+1)^3*2^(4*x.k))*(logSize x)^e := by
  obtain ⟨A,e,hRate⟩ := actual_common_word hg
  refine ⟨A,e,?_⟩
  intro x hm hQv hp
  dsimp only
  intro cursor hc outer ho inner hi
  have hW := GeneralPaperCompilerReference.positive_width C d x
  have hWords := GeneralPaperCompilerReference.local_words C d x
  have hScatter : binaryWordWidth ((GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet x.m x.k).lambda x.k).rows+
      (GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet x.m x.k).lambda x.k).rows+1)≤
      GeneralPaperCompilerReference.width C d x :=
    (binaryWordWidth_mono (show
      (GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet x.m x.k).lambda x.k).rows+
        (GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet x.m x.k).lambda x.k).rows+1≤
      2*(GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet x.m x.k).lambda x.k).rows+
        (GeneralPaperProxyParameters.prepare x.m x.k).K+x.m+1 by omega)).trans hWords.2.2.2.2.2.2.2
  have h := (GeneralPaperSourcePreparedPairOwners.bounded model (GeneralPaperCompilerReference.width C d x) x.k x.Qv hQv x.weights hp x.weight_sum x.b
    C d x.B hg hm x.hb x.hB hW hWords.2.1 hWords.2.2.1 hWords.2.2.2.1 hWords.1 hWords.2.2.2.2.1 hWords.2.2.2.2.2.1 hScatter
    cursor hc outer ho inner hi).1
  exact h.trans ((Nat.le_add_left _ _).trans (hRate x))

theorem retained_construction {m : ℕ} (model : RationalCostModel) (C d W k Qv B : ℕ)
    (hQv : 0<Qv) (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv) (b : ℚ)
    (oldOwner : ℕ) (hOld : oldOwner≤GeneralPaperSourceCompilerPairStorageRates.reservation model C d W m k Qv)
    (hNew : ∀ cursor hc outer ho inner hi,GeneralPaperSourcePreparedPairOwners.window model W k Qv hQv weights hp hs b cursor hc outer ho inner hi≤
      GeneralPaperSourcePreparedPairOwners.profile model C d W m k Qv B) :
    ∀ cursor hc outer ho inner hi,oldOwner+GeneralPaperSourcePreparedPairOwners.window model W k Qv hQv weights hp hs b cursor hc outer ho inner hi≤
      reservation model C d W m k Qv B := by
  intro cursor hc outer ho inner hi
  exact Nat.add_le_add hOld (hNew cursor hc outer ho inner hi)

end Blotto.GeneralPaperSourcePreparedPairOwnerRates
