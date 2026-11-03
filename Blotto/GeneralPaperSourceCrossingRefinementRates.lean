import Blotto.GeneralPaperCrossingRefinementStorage
import Blotto.GeneralPaperSourceCrossingPreparationRates

/-! Full crossing refinement, including every preparation phase, native
search/query window and enclosing optional-bracket return, has source
degree (3,0,4). Retaining query owners and two basis representations keeps
the same degree. Actual reached-stage and global compiler lifetime/capacity
joins remain separate requirements. -/
namespace Blotto.GeneralPaperSourceCrossingRefinementRates
open GeneralPaperSourceWordGrowth GeneralPaperSourceSoftBounds GeneralPaperSourceRateAlgebra
open GeneralPaperConstructedWordGrowth GeneralPaperCompilerReferenceGrowth
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

theorem scaling (model : RationalCostModel) (n R : ℕ) (E Q : ℕ → ℕ)
    (hE : GeneralPaperReferenceScaling.Scale E) (hQ : GeneralPaperReferenceScaling.Scale Q) :
    GeneralPaperReferenceScaling.Scale (fun W => GeneralPaperCrossingRefinementStorage.profile model W n R (E W) (Q W)) := by
  have hP := GeneralPaperSourceCrossingPreparationRates.scaling model n R
  have hS := GeneralPaperSourceSearchStorageRates.scaling model n R E Q hE hQ
  unfold GeneralPaperCrossingRefinementStorage.profile GeneralPaperCrossingPreparationStorage.ownersProfile
    GeneralPaperCrossingRefinementStorage.callerProfile GeneralPaperCrossingRefinementStorage.metadataCap
    GeneralPaperPricedCrossingRefinement.profile GeneralPaperPricedCrossingRefinement.searchProfile
    GeneralPaperPricedCrossingArray.profile GeneralPaperPricedCrossingSort.profile GeneralPaperPricedSort.profile
    GeneralPaperEncodedScalarStorage.natBits
  fun_prop

theorem model_mono (actual upper : RationalCostModel) (h : ∀ n,actual.rat n≤upper.rat n) (W n R E F Q U : ℕ)
    (hE : E≤F) (hQ : Q≤U) :
    GeneralPaperCrossingRefinementStorage.profile actual W n R E Q≤GeneralPaperCrossingRefinementStorage.profile upper W n R F U := by
  have hP := GeneralPaperSourceCrossingPreparationRates.model_mono actual upper h W n R
  have hS := GeneralPaperSourceSearchStorageRates.model_mono actual upper h W n R E F Q U hE hQ
  unfold GeneralPaperCrossingRefinementStorage.profile GeneralPaperCrossingPreparationStorage.ownersProfile
    GeneralPaperCrossingRefinementStorage.callerProfile GeneralPaperCrossingRefinementStorage.metadataCap
    GeneralPaperPricedCrossingRefinement.profile GeneralPaperPricedCrossingRefinement.searchProfile
    GeneralPaperPricedCrossingArray.profile GeneralPaperPricedCrossingSort.profile GeneralPaperPricedSort.profile
    GeneralPaperEncodedScalarStorage.natBits
  gcongr <;> first | exact hP | exact hS | exact h _

def sourceProfile (model : RationalCostModel) (W m k : ℕ) : ℕ :=
  GeneralPaperCrossingRefinementStorage.profile model W
    (((GeneralPaperProxyParameters.prepare m k).S+1)*((GeneralPaperProxyParameters.prepare m k).K*(GeneralPaperProxyParameters.prepare m k).K))
    (GeneralPaperSourceRayStorageWidth.width m k)
    (GeneralPaperCrossingSearchStorage.nativePrice model W m (GeneralPaperProxyParameters.prepare m k).K (GeneralPaperProxyParameters.prepare m k).S
      (GeneralPaperSourceRayStorageWidth.width m k))
    (GeneralPaperSourceEndpointOwnerStorage.profile model W m k)

theorem source_scaling (model : RationalCostModel) (m k : ℕ) :
    GeneralPaperReferenceScaling.Scale (fun W => sourceProfile model W m k) := by
  have hE : GeneralPaperReferenceScaling.Scale (fun W => GeneralPaperCrossingSearchStorage.nativePrice model W m
      (GeneralPaperProxyParameters.prepare m k).K (GeneralPaperProxyParameters.prepare m k).S (GeneralPaperSourceRayStorageWidth.width m k)) := by
    unfold GeneralPaperCrossingSearchStorage.nativePrice
    fun_prop
  exact scaling model _ _ _ _ hE (GeneralPaperSourceEndpointOwnerRates.scaling model m k)

theorem source_mono (actual upper : RationalCostModel) (h : ∀ n,actual.rat n≤upper.rat n) (W m k : ℕ) :
    sourceProfile actual W m k≤sourceProfile upper W m k := by
  apply model_mono actual upper h W _ _ _ _ _ _ _ (GeneralPaperSourceEndpointOwnerRates.model_mono actual upper h W m k)
  unfold GeneralPaperCrossingSearchStorage.nativePrice
  gcongr
  exact h _

def certificate (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    Certificate (fun x => sourceProfile (GeneralPaperFastRationalMajorant.model C d) (W x) x.m x.k) := by
  have hr : Rated W 0 0 0 := poly (poly_tight W hW)
  have hs := of_tight hW
  have hR := GeneralPaperSourceSharpOperandRates.ray_width
  have hsR := GeneralPaperSourceRayStorageRates.width_small
  have hP := (GeneralPaperSourceCrossingPreparationRates.certificate C d W hW).bound
  have hS := (GeneralPaperSourceSearchStorageRates.certificate C d W hW).bound
  refine ⟨_,_,_,by
    unfold sourceProfile GeneralPaperCrossingRefinementStorage.profile GeneralPaperCrossingPreparationStorage.ownersProfile
      GeneralPaperCrossingRefinementStorage.callerProfile GeneralPaperCrossingRefinementStorage.metadataCap
      GeneralPaperPricedCrossingRefinement.profile GeneralPaperPricedCrossingRefinement.searchProfile
      GeneralPaperPricedCrossingArray.profile GeneralPaperPricedCrossingSort.profile GeneralPaperPricedSort.profile
      GeneralPaperCrossingSearchStorage.nativePrice GeneralPaperEncodedScalarStorage.natBits
    dsimp only [GeneralPaperFastRationalMajorant.model]
    source_space⟩

theorem degrees (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    ((certificate C d W hW).fields,(certificate C d W hW).symbols,(certificate C d W hW).accuracy)=(3,0,4) := rfl

theorem actual_rate {actual : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth actual C d)
    (W : Input → ℕ) (hW : Tight W) : Rated (fun x => sourceProfile actual (W x) x.m x.k) 3 0 4 :=
  GeneralPaperSourceSoftBounds.dominated (certificate C d W hW).bound
    (fun x => source_mono actual (GeneralPaperFastRationalMajorant.model C d) (GeneralPaperFastRationalMajorant.dominates hg) (W x) x.m x.k)

def reservation (model : RationalCostModel) (W m k : ℕ) : ℕ :=
  GeneralPaperSourceEndpointOwnerStorage.profile model W m k+sourceProfile model W m k+2*GeneralPaperEncodedBasisStorage.paperProfile W m k

def reservationCertificate (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    Certificate (fun x => reservation (GeneralPaperFastRationalMajorant.model C d) (W x) x.m x.k) := by
  have hOwner := (GeneralPaperSourceSharpOwnerRates.certificate C d W hW).bound
  have hRefinement := (certificate C d W hW).bound
  have hBasis := GeneralPaperBasisStorageRates.profile_rate W hW
  refine ⟨_,_,_,by unfold reservation; source_space⟩

theorem reservation_degrees (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    ((reservationCertificate C d W hW).fields,(reservationCertificate C d W hW).symbols,
      (reservationCertificate C d W hW).accuracy)=(3,0,4) := rfl

theorem reservation_scaling (model : RationalCostModel) (m k : ℕ) :
    GeneralPaperReferenceScaling.Scale (fun W => reservation model W m k) := by
  have ho := GeneralPaperSourceEndpointOwnerRates.scaling model m k
  have hr := source_scaling model m k
  unfold reservation
  fun_prop

theorem reservation_mono (actual upper : RationalCostModel) (h : ∀ n,actual.rat n≤upper.rat n) (W m k : ℕ) :
    reservation actual W m k≤reservation upper W m k :=
  Nat.add_le_add_right (Nat.add_le_add (GeneralPaperSourceEndpointOwnerRates.model_mono actual upper h W m k)
    (source_mono actual upper h W m k)) _

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

end Blotto.GeneralPaperSourceCrossingRefinementRates
