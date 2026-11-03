import Blotto.GeneralPaperRetainedSourceColumnCallerStorage

/-! Complete retained source-column parent arrays and native work fields
sum with all checked child lifetimes at the paper space degree (3,0,4). -/
namespace Blotto.GeneralPaperSourceColumnCallerStorageRates
open GeneralPaperSourceWordGrowth GeneralPaperSourceSoftBounds GeneralPaperSourceRateAlgebra
open GeneralPaperConstructedWordGrowth GeneralPaperCompilerReferenceGrowth
set_option autoImplicit false
set_option maxHeartbeats 7000000
set_option maxRecDepth 16384

def unitPrice (model : RationalCostModel) (W m k : ℕ) : ℕ := GeneralPaperUnitSourceCallerStorage.price W
  (GeneralPaperSourceUnitCallerStorageRates.quantizationPrice model W m k)
  (GeneralPaperSourceUnitCallerStorageRates.normalizationPrice model W m k)
noncomputable def sourceProfile (model : RationalCostModel) (C d W m k Qv : ℕ) : ℕ :=
  GeneralPaperRetainedSourceColumnCallerStorage.profile W m k Qv
    (GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet m k).lambda k).rows
    (GeneralPaperProxyParameters.prepare m k).K (GeneralPaperSourceUnitCallerStorageRates.operandWidth m k)
    (GeneralPaperSourceRowsCallerStorageRates.sourceWorkCap C d W m k Qv) (unitPrice model W m k)

theorem source_model_mono (actual upper : RationalCostModel) (h : ∀ n,actual.rat n≤upper.rat n) (C d W m k Qv : ℕ) :
    sourceProfile actual C d W m k Qv≤sourceProfile upper C d W m k Qv := by
  unfold sourceProfile unitPrice GeneralPaperRetainedSourceColumnCallerStorage.profile
    GeneralPaperRetainedSourceColumnCallerStorage.metadataCap GeneralPaperRetainedSourceColumnCallerStorage.price
    GeneralPaperSourceUnitCallerStorageRates.quantizationPrice GeneralPaperSourceUnitCallerStorageRates.normalizationPrice
    GeneralPaperSourceUnitCallerStorageRates.operandWidth GeneralPaperSourceUnitCallerStorageRates.operandCap GeneralPaperDictionaryNormalizationStorage.price
    GeneralPaperDivisibleColumnsParentStorage.price GeneralPaperDictionaryNormalizationStorage.scalePrice
    GeneralPaperEnclosingSourceOwners.columnsProfile GeneralPaperEnclosingSourceOwners.rowsProfile GeneralPaperQuantizedMatrixParentStorage.price
    GeneralPaperDictionaryNormalizationStorage.fieldPrice GeneralPaperEnclosingSourceOwners.columnProfile
    GeneralPaperQuantizedMatrixParentStorage.callbackPrice GeneralPaperUnitSourceCallerStorage.price GeneralPaperEncodedBasisStorage.arrayProfile
    GeneralPaperEncodedScalarStorage.natBits GeneralPaperQuantizedMatrixParentStorage.fieldPrice GeneralPaperRationalArrayScaleStorage.price
    GeneralPaperColumnInputStorage.price GeneralPaperQuantizedColumnParentStorage.price GeneralPaperRationalArrayScaleStorage.callbackPrice
    GeneralPaperQuantizedAnchorStorage.price GeneralPaperQuantizedLabelScatterStorage.price GeneralPaperRepresentativeSortStorage.price
    GeneralPaperNativeIndexedScatterStorage.price GeneralPaperNativePayloadFillStorage.workCap GeneralPaperNativeRepresentativeSort.profile
    GeneralPaperQuantizedAnchorStorage.callbackPrice GeneralPaperQuantizedLabelScatterStorage.callbackPrice GeneralPaperNativeBlockLabelStorage.price
    GeneralPaperPricedSort.profile GeneralPaperQuantizedAnchorStorage.operandWord GeneralPaperNativeBlockLabelStorage.magnitude
    GeneralPaperNativeGrowingQuotientStorage.workCap
  gcongr <;> exact h _

def certificate (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    Certificate (fun x => sourceProfile (GeneralPaperFastRationalMajorant.model C d) C d (W x) x.m x.k x.Qv) := by
  have hr : Rated W 0 0 0 := poly (poly_tight W hW)
  have hw := of_tight hW
  have hRows := GeneralPaperSourceStaticConstructionRates.sharp_rows
  have hA := GeneralPaperSourceSharpOperandRates.anchor_height
  have hsA := GeneralPaperScoreStorageRates.anchor_small
  have hWork := GeneralPaperSourceRowsCallerStorageRates.work_cap_small C d W hW
  refine ⟨_,_,_,by
    unfold sourceProfile unitPrice GeneralPaperRetainedSourceColumnCallerStorage.profile
      GeneralPaperRetainedSourceColumnCallerStorage.metadataCap GeneralPaperRetainedSourceColumnCallerStorage.price
      GeneralPaperSourceUnitCallerStorageRates.quantizationPrice GeneralPaperSourceUnitCallerStorageRates.normalizationPrice
      GeneralPaperSourceUnitCallerStorageRates.operandWidth GeneralPaperSourceUnitCallerStorageRates.operandCap GeneralPaperDictionaryNormalizationStorage.price
      GeneralPaperDivisibleColumnsParentStorage.price GeneralPaperDictionaryNormalizationStorage.scalePrice
      GeneralPaperEnclosingSourceOwners.columnsProfile GeneralPaperEnclosingSourceOwners.rowsProfile GeneralPaperQuantizedMatrixParentStorage.price
      GeneralPaperDictionaryNormalizationStorage.fieldPrice GeneralPaperEnclosingSourceOwners.columnProfile
      GeneralPaperQuantizedMatrixParentStorage.callbackPrice GeneralPaperUnitSourceCallerStorage.price GeneralPaperEncodedBasisStorage.arrayProfile
      GeneralPaperEncodedScalarStorage.natBits GeneralPaperQuantizedMatrixParentStorage.fieldPrice GeneralPaperRationalArrayScaleStorage.price
      GeneralPaperColumnInputStorage.price GeneralPaperQuantizedColumnParentStorage.price GeneralPaperRationalArrayScaleStorage.callbackPrice
      GeneralPaperQuantizedAnchorStorage.price GeneralPaperQuantizedLabelScatterStorage.price GeneralPaperRepresentativeSortStorage.price
      GeneralPaperNativeIndexedScatterStorage.price GeneralPaperNativePayloadFillStorage.workCap GeneralPaperNativeRepresentativeSort.profile
      GeneralPaperQuantizedAnchorStorage.callbackPrice GeneralPaperQuantizedLabelScatterStorage.callbackPrice GeneralPaperNativeBlockLabelStorage.price
      GeneralPaperPricedSort.profile GeneralPaperQuantizedAnchorStorage.operandWord GeneralPaperNativeBlockLabelStorage.magnitude
      GeneralPaperNativeGrowingQuotientStorage.workCap
    dsimp only [GeneralPaperFastRationalMajorant.model]
    source_space⟩

theorem degrees (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    ((certificate C d W hW).fields,(certificate C d W hW).symbols,(certificate C d W hW).accuracy)=(3,0,4) := rfl

noncomputable def reservation (actual : RationalCostModel) (C d W m k Qv : ℕ) : ℕ :=
  GeneralPaperSourceRowsCallerStorageRates.reservation actual C d W m k Qv+sourceProfile actual C d W m k Qv

def reservationCertificate (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    Certificate (fun x => reservation (GeneralPaperFastRationalMajorant.model C d) C d (W x) x.m x.k x.Qv) := by
  refine ⟨3,0,4,?_⟩
  exact GeneralPaperSourceRateAlgebra.add _ _ 3 0 4 3 0 4
    (GeneralPaperSourceRowsCallerStorageRates.reservationCertificate C d W hW).bound (certificate C d W hW).bound

theorem reservation_degrees (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    ((reservationCertificate C d W hW).fields,(reservationCertificate C d W hW).symbols,(reservationCertificate C d W hW).accuracy)=(3,0,4) := rfl

theorem reservation_mono (actual upper : RationalCostModel) (h : ∀ n,actual.rat n≤upper.rat n) (C d W m k Qv : ℕ) :
    reservation actual C d W m k Qv≤reservation upper C d W m k Qv :=
  Nat.add_le_add (GeneralPaperSourceRowsCallerStorageRates.reservation_mono actual upper h C d W m k Qv) (source_model_mono actual upper h C d W m k Qv)

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

end Blotto.GeneralPaperSourceColumnCallerStorageRates
