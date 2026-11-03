import Blotto.GeneralPaperRayRefinementResidents

/-! Sharp selected-source resident rates. A complete retained crossing
batch/list/array has soft degree (2,0,4). Together with the already checked
per-query owners/predicate and two retained basis representations, these
components fit degree (3,0,4). This is not a full construction/lifetime or
global address-capacity theorem; unjoined temporaries remain required. -/
namespace Blotto.GeneralPaperSourceRefinementResidentRates
open GeneralPaperSourceWordGrowth GeneralPaperSourceSoftBounds GeneralPaperSourceRateAlgebra
open GeneralPaperConstructedWordGrowth GeneralPaperCompilerReferenceGrowth
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxRecDepth 8192

theorem scaling (model : RationalCostModel) (n R : ℕ) :
    GeneralPaperReferenceScaling.Scale (fun W => GeneralPaperRayRefinementResidents.profile model W n R) := by
  unfold GeneralPaperRayRefinementResidents.profile GeneralPaperRayRefinementResidents.listProfile GeneralPaperRayRefinementResidents.arrayProfile
      GeneralPaperRayRefinementResidents.metadataCap GeneralPaperPricedCrossingArray.profile GeneralPaperPricedCrossingSort.profile GeneralPaperPricedSort.profile
      GeneralPaperEncodedScalarStorage.natBits
  fun_prop

theorem model_mono (actual upper : RationalCostModel) (h : ∀ n,actual.rat n≤upper.rat n) (W n R : ℕ) :
    GeneralPaperRayRefinementResidents.profile actual W n R≤GeneralPaperRayRefinementResidents.profile upper W n R := by
  unfold GeneralPaperRayRefinementResidents.profile GeneralPaperRayRefinementResidents.listProfile GeneralPaperRayRefinementResidents.arrayProfile
      GeneralPaperRayRefinementResidents.metadataCap GeneralPaperPricedCrossingArray.profile GeneralPaperPricedCrossingSort.profile GeneralPaperPricedSort.profile
      GeneralPaperEncodedScalarStorage.natBits
  gcongr <;> exact h _

def sourceProfile (model : RationalCostModel) (W m k : ℕ) : ℕ :=
  GeneralPaperRayRefinementResidents.profile model W
    (((GeneralPaperProxyParameters.prepare m k).S+1)*((GeneralPaperProxyParameters.prepare m k).K*(GeneralPaperProxyParameters.prepare m k).K))
    (GeneralPaperSourceRayStorageWidth.width m k)

def certificate (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    Certificate (fun x => sourceProfile (GeneralPaperFastRationalMajorant.model C d) (W x) x.m x.k) := by
  have hr : Rated W 0 0 0 := poly (poly_tight W hW)
  have hs := of_tight hW
  have hR := GeneralPaperSourceSharpOperandRates.ray_width
  have hsR := GeneralPaperSourceRayStorageRates.width_small
  refine ⟨_,_,_,by
    unfold sourceProfile GeneralPaperRayRefinementResidents.profile GeneralPaperRayRefinementResidents.listProfile GeneralPaperRayRefinementResidents.arrayProfile
      GeneralPaperRayRefinementResidents.metadataCap GeneralPaperPricedCrossingArray.profile GeneralPaperPricedCrossingSort.profile GeneralPaperPricedSort.profile
      GeneralPaperEncodedScalarStorage.natBits
    dsimp only [GeneralPaperFastRationalMajorant.model]
    source_space⟩

theorem degrees (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    ((certificate C d W hW).fields,(certificate C d W hW).symbols,(certificate C d W hW).accuracy)=(2,0,4) := rfl

theorem actual_rate {actual : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth actual C d)
    (W : Input → ℕ) (hW : Tight W) : Rated (fun x => sourceProfile actual (W x) x.m x.k) 2 0 4 :=
  GeneralPaperSourceSoftBounds.dominated (certificate C d W hW).bound
    (fun x => model_mono actual (GeneralPaperFastRationalMajorant.model C d) (GeneralPaperFastRationalMajorant.dominates hg)
      (W x) _ _)

def reservation (model : RationalCostModel) (W m k : ℕ) : ℕ :=
  GeneralPaperSourceEndpointOwnerStorage.profile model W m k+sourceProfile model W m k+
    2*GeneralPaperEncodedBasisStorage.paperProfile W m k

def reservationCertificate (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    Certificate (fun x => reservation (GeneralPaperFastRationalMajorant.model C d) (W x) x.m x.k) := by
  have hOwner := (GeneralPaperSourceSharpOwnerRates.certificate C d W hW).bound
  have hBatch := (certificate C d W hW).bound
  have hBasis := GeneralPaperBasisStorageRates.profile_rate W hW
  refine ⟨_,_,_,by
    unfold reservation
    source_space⟩

theorem reservation_degrees (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    ((reservationCertificate C d W hW).fields,(reservationCertificate C d W hW).symbols,
      (reservationCertificate C d W hW).accuracy)=(3,0,4) := rfl

theorem reservation_scaling (model : RationalCostModel) (m k : ℕ) :
    GeneralPaperReferenceScaling.Scale (fun W => reservation model W m k) := by
  have ho := GeneralPaperSourceEndpointOwnerRates.scaling model m k
  have hb := scaling model (((GeneralPaperProxyParameters.prepare m k).S+1)*
    ((GeneralPaperProxyParameters.prepare m k).K*(GeneralPaperProxyParameters.prepare m k).K)) (GeneralPaperSourceRayStorageWidth.width m k)
  unfold reservation sourceProfile
  fun_prop

theorem reservation_mono (actual upper : RationalCostModel) (h : ∀ n,actual.rat n≤upper.rat n) (W m k : ℕ) :
    reservation actual W m k≤reservation upper W m k :=
  Nat.add_le_add_right (Nat.add_le_add (GeneralPaperSourceEndpointOwnerRates.model_mono actual upper h W m k)
    (model_mono actual upper h W _ _)) _

theorem actual_reservation_rate {actual : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth actual C d)
    (W : Input → ℕ) (hW : Tight W) : Rated (fun x => reservation actual (W x) x.m x.k) 3 0 4 :=
  GeneralPaperSourceSoftBounds.dominated (reservationCertificate C d W hW).bound
    (fun x => reservation_mono actual (GeneralPaperFastRationalMajorant.model C d) (GeneralPaperFastRationalMajorant.dominates hg) (W x) x.m x.k)

theorem reservation_at_one_small (C d : ℕ) : Small (fun x => reservation (GeneralPaperFastRationalMajorant.model C d) 1 x.m x.k) := by
  apply GeneralPaperSourceRowsStorageRates.soft_small (reservationCertificate C d (fun _ => 1) (tight_constant 1)).bound
  unfold monomial GeneralPaperNativeSourceRates.fields GeneralPaperNativeSourceRates.symbols GeneralPaperNativeSourceRates.accuracy
  fun_prop

theorem actual_common_word {actual : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth actual C d) :
    ∃ A e : ℕ,∀ x,reservation actual (GeneralPaperCompilerReference.width C d x) x.m x.k≤
      A*(x.m+1)^3*2^(4*x.k)*(logSize x)^e := by
  rcases actual_reservation_rate hg (GeneralPaperCompilerReference.width C d) (width_tight C d) with ⟨A,e,hA⟩
  refine ⟨A,e,?_⟩
  intro x
  have he : (GeneralPaperNativeSourceRates.accuracy x)^4=2^(4*x.k) := by
    simp only [GeneralPaperNativeSourceRates.accuracy,←pow_mul,Nat.mul_comm x.k 4]
  simpa only [monomial,pow_zero,Nat.mul_one,GeneralPaperNativeSourceRates.fields,he,Nat.mul_assoc] using hA x

end Blotto.GeneralPaperSourceRefinementResidentRates

