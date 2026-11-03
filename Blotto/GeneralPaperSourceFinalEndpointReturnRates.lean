import Blotto.GeneralPaperBasisContinuationReturnStorage

/-! Complete raw endpoint and final basis-continuation parent returns
fit degree (3,0,3). Full cache/basis/optional-vector owners and all native
return fields sum with the preceding reserves, preserving (3,0,4). -/
namespace Blotto.GeneralPaperSourceFinalEndpointReturnRates
open GeneralPaperSourceWordGrowth GeneralPaperSourceSoftBounds GeneralPaperSourceRateAlgebra
open GeneralPaperConstructedWordGrowth GeneralPaperCompilerReferenceGrowth
set_option autoImplicit false
set_option maxHeartbeats 7000000
set_option maxRecDepth 8192

def operandWidth (m k : ℕ) : ℕ := GeneralPaperSourceFinalCheckStorageRates.operandWidth m k
def affinePrice (model : RationalCostModel) (W m k : ℕ) : ℕ :=
  GeneralPaperBasisAffineStorage.price model W (m*((GeneralPaperProxyParameters.prepare m k).K-1)) (operandWidth m k)
def sourceProfile (model : RationalCostModel) (W m k : ℕ) : ℕ :=
  let T := (GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet m k).lambda k).rows
  let K := (GeneralPaperProxyParameters.prepare m k).K
  let S := (GeneralPaperProxyParameters.prepare m k).S
  let R := operandWidth m k
  let F := affinePrice model W m k
  GeneralPaperRawEndpointReturnStorage.profile model W T m K S R F+
    GeneralPaperBasisContinuationReturnStorage.profile model W T m K S R F
      (GeneralPaperEncodedBasisStorage.paperProfile W m k)

theorem source_scaling (model : RationalCostModel) (m k : ℕ) : GeneralPaperReferenceScaling.Scale (fun W => sourceProfile model W m k) := by
  have hBasis := GeneralPaperEncodedBasisStorage.paper_profile_scale m k
  unfold sourceProfile affinePrice operandWidth
    GeneralPaperBasisAffineStorage.price GeneralPaperBasisContinuationReturnStorage.profile GeneralPaperRawEndpointReturnStorage.profile
    GeneralPaperBasisContinuationReturnStorage.metadataCap GeneralPaperRawEndpointReturnStorage.cacheProfile GeneralPaperRawEndpointReturnStorage.metadataCap
    GeneralPaperRawEndpointReturnStorage.optionProfile GeneralPaperEncodedBasisStorage.arrayProfile GeneralPaperEncodedScalarStorage.natBits
    GeneralPaperRawEndpointReturnStorage.price GeneralPaperRawEndpointReturnStorage.evaluationPrice GeneralPaperFinalPolytopeStorage.price
    GeneralPaperFinalPolytopeBits.profile GeneralPaperStaticScanPrice.profile GeneralPaperSourceFinalCheckStorageRates.operandWidth
    GeneralPaperSourceRawAffineStorageRates.operandWidth
  dsimp only
  fun_prop

theorem source_model_mono (actual upper : RationalCostModel) (h : ∀ n,actual.rat n≤upper.rat n) (W m k : ℕ) :
    sourceProfile actual W m k≤sourceProfile upper W m k := by
  unfold sourceProfile affinePrice operandWidth
    GeneralPaperBasisAffineStorage.price GeneralPaperBasisContinuationReturnStorage.profile GeneralPaperRawEndpointReturnStorage.profile
    GeneralPaperBasisContinuationReturnStorage.metadataCap GeneralPaperRawEndpointReturnStorage.cacheProfile GeneralPaperRawEndpointReturnStorage.metadataCap
    GeneralPaperRawEndpointReturnStorage.optionProfile GeneralPaperEncodedBasisStorage.arrayProfile GeneralPaperEncodedScalarStorage.natBits
    GeneralPaperRawEndpointReturnStorage.price GeneralPaperRawEndpointReturnStorage.evaluationPrice GeneralPaperFinalPolytopeStorage.price
    GeneralPaperFinalPolytopeBits.profile GeneralPaperStaticScanPrice.profile GeneralPaperSourceFinalCheckStorageRates.operandWidth
    GeneralPaperSourceRawAffineStorageRates.operandWidth
  dsimp only
  gcongr <;> exact h _

def certificate (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    Certificate (fun x => sourceProfile (GeneralPaperFastRationalMajorant.model C d) (W x) x.m x.k) := by
  have hr : Rated W 0 0 0 := poly (poly_tight W hW)
  have hs := of_tight hW
  have hR := GeneralPaperSourceSharpOperandRates.ray_width
  have hsR := GeneralPaperSourceRayStorageRates.width_small
  have hRows := GeneralPaperSourceStaticConstructionRates.sharp_rows
  have hBasis := GeneralPaperBasisStorageRates.profile_rate W hW
  refine ⟨_,_,_,by
    unfold sourceProfile affinePrice operandWidth
      GeneralPaperBasisAffineStorage.price GeneralPaperBasisContinuationReturnStorage.profile GeneralPaperRawEndpointReturnStorage.profile
      GeneralPaperBasisContinuationReturnStorage.metadataCap GeneralPaperRawEndpointReturnStorage.cacheProfile GeneralPaperRawEndpointReturnStorage.metadataCap
      GeneralPaperRawEndpointReturnStorage.optionProfile GeneralPaperEncodedBasisStorage.arrayProfile GeneralPaperEncodedScalarStorage.natBits
      GeneralPaperRawEndpointReturnStorage.price GeneralPaperRawEndpointReturnStorage.evaluationPrice GeneralPaperFinalPolytopeStorage.price
      GeneralPaperFinalPolytopeBits.profile GeneralPaperStaticScanPrice.profile GeneralPaperSourceFinalCheckStorageRates.operandWidth
      GeneralPaperSourceRawAffineStorageRates.operandWidth
    dsimp only [GeneralPaperFastRationalMajorant.model]
    source_space⟩

theorem degrees (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    ((certificate C d W hW).fields,(certificate C d W hW).symbols,(certificate C d W hW).accuracy)=(3,0,3) := rfl

def reservation (model : RationalCostModel) (W m k : ℕ) : ℕ := GeneralPaperSourceFinalCheckStorageRates.reservation model W m k+sourceProfile model W m k
def reservationCertificate (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    Certificate (fun x => reservation (GeneralPaperFastRationalMajorant.model C d) (W x) x.m x.k) := by
  have hOld := (GeneralPaperSourceFinalCheckStorageRates.reservationCertificate C d W hW).bound
  have hNew := (certificate C d W hW).bound
  refine ⟨_,_,_,by unfold reservation; source_space⟩

theorem reservation_degrees (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    ((reservationCertificate C d W hW).fields,(reservationCertificate C d W hW).symbols,(reservationCertificate C d W hW).accuracy)=(3,0,4) := rfl

theorem reservation_scaling (model : RationalCostModel) (m k : ℕ) : GeneralPaperReferenceScaling.Scale (fun W => reservation model W m k) := by
  have hOld := GeneralPaperSourceFinalCheckStorageRates.reservation_scaling model m k
  have hNew := source_scaling model m k
  unfold reservation
  fun_prop

theorem reservation_mono (actual upper : RationalCostModel) (h : ∀ n,actual.rat n≤upper.rat n) (W m k : ℕ) :
    reservation actual W m k≤reservation upper W m k :=
  Nat.add_le_add (GeneralPaperSourceFinalCheckStorageRates.reservation_mono actual upper h W m k) (source_model_mono actual upper h W m k)

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

end Blotto.GeneralPaperSourceFinalEndpointReturnRates
