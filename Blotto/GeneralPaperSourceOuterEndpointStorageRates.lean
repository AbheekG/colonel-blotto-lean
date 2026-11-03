import Blotto.GeneralPaperSourceEndpointContinuationReturnBounds

/-! Literal outer endpoint parent ownership fits degree (3,0,3).
Actual scalar/input/basis/point owners and encoded work metadata SUM with
all earlier reserves, preserving the common-word paper space (3,0,4). -/
namespace Blotto.GeneralPaperSourceOuterEndpointStorageRates
open GeneralPaperSourceWordGrowth GeneralPaperSourceSoftBounds GeneralPaperSourceRateAlgebra
open GeneralPaperConstructedWordGrowth GeneralPaperCompilerReferenceGrowth
set_option autoImplicit false
set_option maxHeartbeats 7000000
set_option maxRecDepth 8192

def price (model : RationalCostModel) (W m k : ℕ) : ℕ :=
  GeneralPaperSourceInitializerReturnStorageRates.inputPrice model W m k+
    GeneralPaperSourceBasisControllerStorageRates.workPrice model W m k+
    GeneralPaperSourceEndpointContinuationReturnBounds.price model W m k+
    7*model.rat (GeneralPaperRetainedEndpointBitBounds.priceWidth (GeneralPaperProxyParameters.prepare m k).qbar)+144*W
def sourceProfile (model : RationalCostModel) (W m k : ℕ) : ℕ :=
  GeneralPaperOuterEndpointFrameStorage.profile W
    (GeneralPaperSourceEndpointScalarStorageRates.sourceProfile model W m k)
    (GeneralPaperSourceInitializerReturnStorageRates.sourceProfile model W m k)
    (GeneralPaperEncodedBasisStorage.paperProfile W m k)
    (GeneralPaperSourceEndpointContinuationReturnBounds.pointProfile W m k) (price model W m k)

theorem source_scaling (model : RationalCostModel) (m k : ℕ) : GeneralPaperReferenceScaling.Scale (fun W => sourceProfile model W m k) := by
  have hScalar := GeneralPaperSourceEndpointScalarStorageRates.source_scaling model m k
  have hInput := GeneralPaperSourceInitializerReturnStorageRates.source_scaling model m k
  have hBasis := GeneralPaperEncodedBasisStorage.paper_profile_scale m k
  unfold sourceProfile price GeneralPaperOuterEndpointFrameStorage.profile
    GeneralPaperRetainedEndpointBitBounds.priceWidth GeneralPaperSourceBasisControllerStorageRates.workPrice GeneralPaperSourceEndpointContinuationReturnBounds.pointProfile
    GeneralPaperSourceEndpointContinuationReturnBounds.price GeneralPaperSourceInitializerReturnStorageRates.inputPrice GeneralPaperBasisControllerBits.profile
    GeneralPaperEncodedScalarStorage.natBits GeneralPaperOuterEndpointFrameStorage.metadataCap GeneralPaperRawEndpointReturnStorage.optionProfile
    GeneralPaperRawEndpointReturnStorage.price GeneralPaperSourceBasisControllerStorageRates.operandWidth GeneralPaperSourceFinalEndpointReturnRates.affinePrice
    GeneralPaperSourceInitializerReturnStorageRates.controlPrice GeneralPaperSourceInitializerReturnStorageRates.gridPrice GeneralPaperBasisAffineStorage.price
    GeneralPaperBasisStepBits.profile GeneralPaperEncodedBasisStorage.arrayProfile GeneralPaperInitializerControlStorage.price
    GeneralPaperRawEndpointReturnStorage.evaluationPrice GeneralPaperSourceFinalEndpointReturnRates.operandWidth GeneralPaperSourceInitializerControlStorageRates.operandWidth
    GeneralPaperSourceInitializerReturnStorageRates.packedPrice GeneralPaperSourceInitializerReturnStorageRates.storedPrice GeneralPaperBasisGridPackingPrice.profile
    GeneralPaperEndpointPriceControl.profile GeneralPaperFinalPolytopeStorage.price GeneralPaperSourceBasisGridPackingStorageRates.operandWidth
    GeneralPaperSourceFinalCheckStorageRates.operandWidth GeneralPaperSourceInitializerTableStorageRates.operandWidth GeneralPaperFinalPolytopeBits.profile
    GeneralPaperHighSearchPriceFacts.profile GeneralPaperSourceRawAffineStorageRates.operandWidth GeneralPaperFinalRefinementPrice.profile
    GeneralPaperHighBlockerPrice.profile GeneralPaperHighSearchPriceControl.profile GeneralPaperParametricPriceProfiles.profile
    GeneralPaperStaticScanPrice.profile GeneralPaperFinalRefinementPrice.envelope GeneralPaperFixedViolationPrice.profile
    GeneralPaperParametricRecursionPrice.profile GeneralPaperParametricStageBits.profile GeneralPaperAffineStepPrice.profile
  dsimp only
  fun_prop

theorem source_model_mono (actual upper : RationalCostModel) (h : ∀ n,actual.rat n≤upper.rat n) (W m k : ℕ) :
    sourceProfile actual W m k≤sourceProfile upper W m k := by
  have hScalar := GeneralPaperSourceEndpointScalarStorageRates.source_model_mono actual upper h W m k
  have hInput := GeneralPaperSourceInitializerReturnStorageRates.source_model_mono actual upper h W m k
  unfold sourceProfile price GeneralPaperOuterEndpointFrameStorage.profile
    GeneralPaperRetainedEndpointBitBounds.priceWidth GeneralPaperSourceBasisControllerStorageRates.workPrice GeneralPaperSourceEndpointContinuationReturnBounds.pointProfile
    GeneralPaperSourceEndpointContinuationReturnBounds.price GeneralPaperSourceInitializerReturnStorageRates.inputPrice GeneralPaperBasisControllerBits.profile
    GeneralPaperEncodedScalarStorage.natBits GeneralPaperOuterEndpointFrameStorage.metadataCap GeneralPaperRawEndpointReturnStorage.optionProfile
    GeneralPaperRawEndpointReturnStorage.price GeneralPaperSourceBasisControllerStorageRates.operandWidth GeneralPaperSourceFinalEndpointReturnRates.affinePrice
    GeneralPaperSourceInitializerReturnStorageRates.controlPrice GeneralPaperSourceInitializerReturnStorageRates.gridPrice GeneralPaperBasisAffineStorage.price
    GeneralPaperBasisStepBits.profile GeneralPaperEncodedBasisStorage.arrayProfile GeneralPaperInitializerControlStorage.price
    GeneralPaperRawEndpointReturnStorage.evaluationPrice GeneralPaperSourceFinalEndpointReturnRates.operandWidth GeneralPaperSourceInitializerControlStorageRates.operandWidth
    GeneralPaperSourceInitializerReturnStorageRates.packedPrice GeneralPaperSourceInitializerReturnStorageRates.storedPrice GeneralPaperBasisGridPackingPrice.profile
    GeneralPaperEndpointPriceControl.profile GeneralPaperFinalPolytopeStorage.price GeneralPaperSourceBasisGridPackingStorageRates.operandWidth
    GeneralPaperSourceFinalCheckStorageRates.operandWidth GeneralPaperSourceInitializerTableStorageRates.operandWidth GeneralPaperFinalPolytopeBits.profile
    GeneralPaperHighSearchPriceFacts.profile GeneralPaperSourceRawAffineStorageRates.operandWidth GeneralPaperFinalRefinementPrice.profile
    GeneralPaperHighBlockerPrice.profile GeneralPaperHighSearchPriceControl.profile GeneralPaperParametricPriceProfiles.profile
    GeneralPaperStaticScanPrice.profile GeneralPaperFinalRefinementPrice.envelope GeneralPaperFixedViolationPrice.profile
    GeneralPaperParametricRecursionPrice.profile GeneralPaperParametricStageBits.profile GeneralPaperAffineStepPrice.profile
  dsimp only
  gcongr <;> first | exact hScalar | exact hInput | exact h _

def certificate (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    Certificate (fun x => sourceProfile (GeneralPaperFastRationalMajorant.model C d) (W x) x.m x.k) := by
  have hr : Rated W 0 0 0 := poly (poly_tight W hW)
  have hs := of_tight hW
  have hA := GeneralPaperSourceSharpOperandRates.anchor_height
  have hsA : Small (fun x => GeneralPaperSourceScoreHeights.anchorHeight x.m x.k) := by
    apply GeneralPaperSourceRowsStorageRates.soft_small hA
    unfold monomial GeneralPaperNativeSourceRates.fields GeneralPaperNativeSourceRates.symbols GeneralPaperNativeSourceRates.accuracy
    fun_prop
  have hGrid : Rated (fun x => GeneralPaperSourceRayStorageWidth.gridWord x.m x.k) 1 0 1 := by
    apply GeneralPaperSourceSoftBounds.dominated GeneralPaperSourceSharpOperandRates.ray_width
    intro x
    unfold GeneralPaperSourceRayStorageWidth.width GeneralPaperSourceRayStorageWidth.rootWidth
    omega
  have hsGrid : Small (fun x => GeneralPaperSourceRayStorageWidth.gridWord x.m x.k) := by
    apply GeneralPaperSourceWordGrowth.dominated GeneralPaperSourceRayStorageRates.width_small
    intro x
    unfold GeneralPaperSourceRayStorageWidth.width GeneralPaperSourceRayStorageWidth.rootWidth
    omega
  have hScalar := (GeneralPaperSourceEndpointScalarStorageRates.certificate C d W hW).bound
  have hInput := (GeneralPaperSourceInitializerReturnStorageRates.certificate C d W hW).bound
  have hBasis := GeneralPaperBasisStorageRates.profile_rate W hW
  have hR := GeneralPaperSourceSharpOperandRates.ray_width
  have hsR := GeneralPaperSourceRayStorageRates.width_small
  have hRows := GeneralPaperSourceStaticConstructionRates.sharp_rows
  refine ⟨_,_,_,by
    unfold sourceProfile price GeneralPaperOuterEndpointFrameStorage.profile
      GeneralPaperRetainedEndpointBitBounds.priceWidth GeneralPaperSourceBasisControllerStorageRates.workPrice GeneralPaperSourceEndpointContinuationReturnBounds.pointProfile
      GeneralPaperSourceEndpointContinuationReturnBounds.price GeneralPaperSourceInitializerReturnStorageRates.inputPrice GeneralPaperBasisControllerBits.profile
      GeneralPaperEncodedScalarStorage.natBits GeneralPaperOuterEndpointFrameStorage.metadataCap GeneralPaperRawEndpointReturnStorage.optionProfile
      GeneralPaperRawEndpointReturnStorage.price GeneralPaperSourceBasisControllerStorageRates.operandWidth GeneralPaperSourceFinalEndpointReturnRates.affinePrice
      GeneralPaperSourceInitializerReturnStorageRates.controlPrice GeneralPaperSourceInitializerReturnStorageRates.gridPrice GeneralPaperBasisAffineStorage.price
      GeneralPaperBasisStepBits.profile GeneralPaperEncodedBasisStorage.arrayProfile GeneralPaperInitializerControlStorage.price
      GeneralPaperRawEndpointReturnStorage.evaluationPrice GeneralPaperSourceFinalEndpointReturnRates.operandWidth GeneralPaperSourceInitializerControlStorageRates.operandWidth
      GeneralPaperSourceInitializerReturnStorageRates.packedPrice GeneralPaperSourceInitializerReturnStorageRates.storedPrice GeneralPaperBasisGridPackingPrice.profile
      GeneralPaperEndpointPriceControl.profile GeneralPaperFinalPolytopeStorage.price GeneralPaperSourceBasisGridPackingStorageRates.operandWidth
      GeneralPaperSourceFinalCheckStorageRates.operandWidth GeneralPaperSourceInitializerTableStorageRates.operandWidth GeneralPaperFinalPolytopeBits.profile
      GeneralPaperHighSearchPriceFacts.profile GeneralPaperSourceRawAffineStorageRates.operandWidth GeneralPaperFinalRefinementPrice.profile
      GeneralPaperHighBlockerPrice.profile GeneralPaperHighSearchPriceControl.profile GeneralPaperParametricPriceProfiles.profile
      GeneralPaperStaticScanPrice.profile GeneralPaperFinalRefinementPrice.envelope GeneralPaperFixedViolationPrice.profile
      GeneralPaperParametricRecursionPrice.profile GeneralPaperParametricStageBits.profile GeneralPaperAffineStepPrice.profile
    dsimp only [GeneralPaperFastRationalMajorant.model]
    source_space⟩

theorem degrees (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    ((certificate C d W hW).fields,(certificate C d W hW).symbols,(certificate C d W hW).accuracy)=(3,0,3) := rfl

def reservation (model : RationalCostModel) (W m k : ℕ) : ℕ := GeneralPaperSourceInitializerReturnStorageRates.reservation model W m k+sourceProfile model W m k
def reservationCertificate (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    Certificate (fun x => reservation (GeneralPaperFastRationalMajorant.model C d) (W x) x.m x.k) := by
  have hOld := (GeneralPaperSourceInitializerReturnStorageRates.reservationCertificate C d W hW).bound
  have hNew := (certificate C d W hW).bound
  refine ⟨_,_,_,by unfold reservation; source_space⟩

theorem reservation_degrees (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    ((reservationCertificate C d W hW).fields,(reservationCertificate C d W hW).symbols,(reservationCertificate C d W hW).accuracy)=(3,0,4) := rfl

theorem reservation_scaling (model : RationalCostModel) (m k : ℕ) : GeneralPaperReferenceScaling.Scale (fun W => reservation model W m k) := by
  have hOld := GeneralPaperSourceInitializerReturnStorageRates.reservation_scaling model m k
  have hNew := source_scaling model m k
  unfold reservation
  fun_prop

theorem reservation_mono (actual upper : RationalCostModel) (h : ∀ n,actual.rat n≤upper.rat n) (W m k : ℕ) :
    reservation actual W m k≤reservation upper W m k :=
  Nat.add_le_add (GeneralPaperSourceInitializerReturnStorageRates.reservation_mono actual upper h W m k) (source_model_mono actual upper h W m k)

theorem actual_reservation_rate {actual : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth actual C d)
    (W : Input → ℕ) (hW : Tight W) : Rated (fun x => reservation actual (W x) x.m x.k) 3 0 4 :=
  GeneralPaperSourceSoftBounds.dominated (reservationCertificate C d W hW).bound
    (fun x => reservation_mono actual (GeneralPaperFastRationalMajorant.model C d) (GeneralPaperFastRationalMajorant.dominates hg) (W x) x.m x.k)

theorem reservation_at_one_small (C d : ℕ) : Small (fun x => reservation (GeneralPaperFastRationalMajorant.model C d) 1 x.m x.k) := by
  apply GeneralPaperSourceRowsStorageRates.soft_small (reservationCertificate C d (fun _ => 1) (tight_constant 1)).bound
  unfold monomial GeneralPaperNativeSourceRates.fields GeneralPaperNativeSourceRates.symbols GeneralPaperNativeSourceRates.accuracy
  fun_prop

theorem actual_common_word {actual : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth actual C d) :
    ∃ A e : ℕ,∀ x,reservation actual (GeneralPaperCompilerReference.width C d x) x.m x.k≤A*(x.m+1)^3*2^(4*x.k)*(logSize x)^e := by
  rcases actual_reservation_rate hg (GeneralPaperCompilerReference.width C d) (width_tight C d) with ⟨A,e,hA⟩
  refine ⟨A,e,?_⟩
  intro x
  have he : (GeneralPaperNativeSourceRates.accuracy x)^4=2^(4*x.k) := by simp only [GeneralPaperNativeSourceRates.accuracy,←pow_mul,Nat.mul_comm x.k 4]
  simpa only [monomial,pow_zero,Nat.mul_one,GeneralPaperNativeSourceRates.fields,he,Nat.mul_assoc] using hA x

end Blotto.GeneralPaperSourceOuterEndpointStorageRates
