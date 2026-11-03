import Blotto.GeneralPaperSourceCallerSharpWork

/-! Actual unit-normalization, retained value and scalar cached-constructor
work profiles under the sharp source alphabet. This bounds their genuine
prices separately from the earlier storage and encoded-work-word bounds. -/
namespace Blotto.GeneralPaperUnitCallerSharpWork
open GeneralPaperSourceWordGrowth GeneralPaperSourceSoftBounds GeneralPaperSourceRateAlgebra GeneralPaperNativeSourceRates
open GeneralPaperConstructedWordGrowth
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 16384

def unitCertificate (C d : ℕ) (W : Input → ℕ) (hW : Tight W) : Certificate
    (fun x => GeneralPaperSourceColumnCallerStorageRates.unitPrice (GeneralPaperFastRationalMajorant.model C d) (W x) x.m x.k) := by
  have hr : Rated W 0 0 0 := poly (poly_tight W hW)
  have hs := of_tight hW
  have hRows := GeneralPaperSourceStaticConstructionRates.sharp_rows
  have hA := GeneralPaperSourceSharpOperandRates.anchor_height
  have hsA := GeneralPaperScoreStorageRates.anchor_small
  refine ⟨_,_,_,by
    dsimp only [GeneralPaperSourceColumnCallerStorageRates.unitPrice,
      GeneralPaperSourceUnitCallerStorageRates.sourceProfile,
      GeneralPaperSourceUnitCallerStorageRates.quantizationPrice,
      GeneralPaperSourceUnitCallerStorageRates.normalizationPrice,
      GeneralPaperSourceUnitCallerStorageRates.operandWidth,
      GeneralPaperSourceUnitCallerStorageRates.operandCap,
      GeneralPaperDictionaryNormalizationStorage.price,
      GeneralPaperDivisibleColumnsParentStorage.price,
      GeneralPaperUnitSourceCallerStorage.profile,
      GeneralPaperDictionaryNormalizationStorage.scalePrice,
      GeneralPaperEnclosingSourceOwners.columnsProfile,
      GeneralPaperEnclosingSourceOwners.rowsProfile,
      GeneralPaperQuantizedMatrixParentStorage.price,
      GeneralPaperUnitSourceCallerStorage.metadataCap,
      GeneralPaperDictionaryNormalizationStorage.fieldPrice,
      GeneralPaperEnclosingSourceOwners.columnProfile,
      GeneralPaperQuantizedMatrixParentStorage.callbackPrice,
      GeneralPaperUnitSourceCallerStorage.price,
      GeneralPaperEncodedBasisStorage.arrayProfile,
      GeneralPaperEncodedScalarStorage.natBits,
      GeneralPaperQuantizedMatrixParentStorage.fieldPrice,
      GeneralPaperRationalArrayScaleStorage.price,
      GeneralPaperColumnInputStorage.price,
      GeneralPaperQuantizedColumnParentStorage.price,
      GeneralPaperRationalArrayScaleStorage.callbackPrice,
      GeneralPaperQuantizedAnchorStorage.price,
      GeneralPaperQuantizedLabelScatterStorage.price,
      GeneralPaperRepresentativeSortStorage.price,
      GeneralPaperNativeIndexedScatterStorage.price,
      GeneralPaperNativePayloadFillStorage.workCap,
      GeneralPaperNativeRepresentativeSort.profile,
      GeneralPaperQuantizedAnchorStorage.callbackPrice,
      GeneralPaperQuantizedLabelScatterStorage.callbackPrice,
      GeneralPaperNativeBlockLabelStorage.price,
      GeneralPaperPricedSort.profile,
      GeneralPaperQuantizedAnchorStorage.operandWord,
      GeneralPaperNativeBlockLabelStorage.magnitude,
      GeneralPaperNativeGrowingQuotientStorage.workCap,
      GeneralPaperFastRationalMajorant.model]
    source_space⟩

def valuesCertificate (C d : ℕ) (W : Input → ℕ) (hW : Tight W) : Certificate
    (fun x => GeneralPaperRetainedFieldValuesStorage.price (GeneralPaperFastRationalMajorant.model C d) (W x) x.m x.Qv) := by
  have hr : Rated W 0 0 0 := poly (poly_tight W hW)
  have hs := of_tight hW
  refine ⟨_,_,_,by
    dsimp only [GeneralPaperRetainedFieldValuesStorage.price,GeneralPaperRetainedFieldValuesStorage.callbackPrice,
      GeneralPaperRetainedFieldValuesStorage.width,GeneralPaperReducedValueArrayPrice.width,GeneralPaperNativePayloadFillStorage.workCap,GeneralPaperSummaryArrayExecution.arrayWord,GeneralPaperFastRationalMajorant.model]
    source_space⟩

def scalarCertificate (C d : ℕ) (W : Input → ℕ) (hW : Tight W) : Certificate (fun x =>
    GeneralPaperCachedPreparationScalarStorage.decodePrice (GeneralPaperFastRationalMajorant.model C d) (W x)
      (GeneralPaperProxyParameters.prepare x.m x.k).qbar+
    2*GeneralPaperCachedPreparationScalarStorage.sharedPrice (GeneralPaperFastRationalMajorant.model C d) (W x) x.k
      (GeneralPaperCachedBitPairStorage.precision x.m x.k) (alphabet x)+128*W x) := by
  have hCap := GeneralPaperSourceSharpOperandRates.cap_word
  have hL := GeneralPaperSourceSharpOperandRates.alphabet_length
  have hs := of_tight hW
  have hr : Rated W 0 0 0 := poly (poly_tight W hW)
  refine ⟨_,_,_,by
    dsimp only [GeneralPaperCachedPreparationScalarStorage.decodePrice,GeneralPaperCachedPreparationScalarStorage.decodeWidth,
      GeneralPaperCachedPreparationScalarStorage.sharedPrice,GeneralPaperSharedSpanPrice.width,
      GeneralPaperSharedWidthPrice.width,GeneralPaperCachedBitPairStorage.precision,GeneralPaperFastRationalMajorant.model]
    source_space⟩

theorem degrees (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    ((unitCertificate C d W hW).fields,(unitCertificate C d W hW).symbols,(unitCertificate C d W hW).accuracy)=(3,0,4) ∧
      ((valuesCertificate C d W hW).fields,(valuesCertificate C d W hW).symbols,(valuesCertificate C d W hW).accuracy)=(1,0,0) ∧
      ((scalarCertificate C d W hW).fields,(scalarCertificate C d W hW).symbols,(scalarCertificate C d W hW).accuracy)=(1,0,1) := ⟨rfl,rfl,rfl⟩

theorem lift_bit {f : Input → ℕ} {a c : ℕ} (hf : Rated f a 0 c) (ha : a≤3) (hc : c≤6) :
    Soft GeneralPaperSourceCallerSharpWork.bitRate f :=
  rate_mono (weaken hf ha le_rfl hc) (fun x => by
    change monomial 3 0 6 x≤monomial 4 0 5 x+monomial 3 0 6 x;omega)

theorem unit_rate (C d : ℕ) (W : Input → ℕ) (hW : Tight W) : Soft GeneralPaperSourceCallerSharpWork.bitRate
    (fun x => GeneralPaperSourceColumnCallerStorageRates.unitPrice (GeneralPaperFastRationalMajorant.model C d) (W x) x.m x.k) :=
  lift_bit (unitCertificate C d W hW).bound (by decide : 3≤3) (by decide : 4≤6)

theorem values_rate (C d : ℕ) (W : Input → ℕ) (hW : Tight W) : Soft GeneralPaperSourceCallerSharpWork.bitRate
    (fun x => GeneralPaperRetainedFieldValuesStorage.price (GeneralPaperFastRationalMajorant.model C d) (W x) x.m x.Qv) :=
  lift_bit (valuesCertificate C d W hW).bound (by decide : 1≤3) (by decide : 0≤6)

theorem scalar_rate (C d : ℕ) (W : Input → ℕ) (hW : Tight W) : Soft GeneralPaperSourceCallerSharpWork.bitRate (fun x =>
    GeneralPaperCachedPreparationScalarStorage.decodePrice (GeneralPaperFastRationalMajorant.model C d) (W x)
      (GeneralPaperProxyParameters.prepare x.m x.k).qbar+
    2*GeneralPaperCachedPreparationScalarStorage.sharedPrice (GeneralPaperFastRationalMajorant.model C d) (W x) x.k
      (GeneralPaperCachedBitPairStorage.precision x.m x.k) (alphabet x)+128*W x) :=
  lift_bit (scalarCertificate C d W hW).bound (by decide : 1≤3) (by decide : 1≤6)

end Blotto.GeneralPaperUnitCallerSharpWork
