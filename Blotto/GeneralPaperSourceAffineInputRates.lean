import Blotto.GeneralPaperAffineInputStorage

/-! Full affine-input buffers, constructors and retained list ownership
have source degree (2,0,2). Their addition preserves the already checked
cubic-field/fourth-accuracy generation/refinement reservation. -/
namespace Blotto.GeneralPaperSourceAffineInputRates
open GeneralPaperSourceWordGrowth GeneralPaperSourceSoftBounds GeneralPaperSourceRateAlgebra
open GeneralPaperConstructedWordGrowth GeneralPaperCompilerReferenceGrowth
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 8192

theorem height_mono (W m K S R H : ℕ) (hR : R≤H) :
    GeneralPaperAffineInputStorage.profile W m K S R≤GeneralPaperAffineInputStorage.profile W m K S H := by
  unfold GeneralPaperAffineInputStorage.profile GeneralPaperAffineInputStorage.entryProfile
    GeneralPaperAffineInputStorage.listProfile GeneralPaperAffineWitnessStorage.fieldProfile GeneralPaperAffineWitnessStorage.affineProfile
  gcongr

theorem list_le_profile (W m K S R : ℕ) :
    GeneralPaperAffineInputStorage.listProfile W m K S R≤GeneralPaperAffineInputStorage.profile W m K S R := by
  unfold GeneralPaperAffineInputStorage.profile
  omega

theorem scaling (m K S R : ℕ) :
    GeneralPaperReferenceScaling.Scale (fun W => GeneralPaperAffineInputStorage.profile W m K S R) := by
  unfold GeneralPaperAffineInputStorage.profile GeneralPaperAffineInputStorage.entryProfile GeneralPaperAffineInputStorage.listProfile
    GeneralPaperAffineInputStorage.metadataCap GeneralPaperAffineInputStorage.fieldPrice GeneralPaperAffineInputStorage.matrixPrice
    GeneralPaperAffineInputStorage.runPrice GeneralPaperScoreConstructionStorage.constructorProfile
    GeneralPaperAffineWitnessStorage.fieldProfile GeneralPaperAffineWitnessStorage.affineProfile GeneralPaperEncodedScalarStorage.natBits
  fun_prop

def sourceProfile (W m k : ℕ) : ℕ := GeneralPaperAffineInputStorage.profile W m
  (GeneralPaperProxyParameters.prepare m k).K (GeneralPaperProxyParameters.prepare m k).S
  (GeneralPaperSourceRayStorageWidth.width m k)

def certificate (W : Input → ℕ) (hW : Tight W) : Certificate (fun x => sourceProfile (W x) x.m x.k) := by
  have hr : Rated W 0 0 0 := poly (poly_tight W hW)
  have hs := of_tight hW
  have hR := GeneralPaperSourceSharpOperandRates.ray_width
  have hsR := GeneralPaperSourceRayStorageRates.width_small
  refine ⟨_,_,_,by
    unfold sourceProfile GeneralPaperAffineInputStorage.profile GeneralPaperAffineInputStorage.entryProfile GeneralPaperAffineInputStorage.listProfile
      GeneralPaperAffineInputStorage.metadataCap GeneralPaperAffineInputStorage.fieldPrice GeneralPaperAffineInputStorage.matrixPrice
      GeneralPaperAffineInputStorage.runPrice GeneralPaperScoreConstructionStorage.constructorProfile
      GeneralPaperAffineWitnessStorage.fieldProfile GeneralPaperAffineWitnessStorage.affineProfile GeneralPaperEncodedScalarStorage.natBits
    source_space⟩

theorem degrees (W : Input → ℕ) (hW : Tight W) :
    ((certificate W hW).fields,(certificate W hW).symbols,(certificate W hW).accuracy)=(2,0,2) := rfl

def reservation (model : RationalCostModel) (W m k : ℕ) : ℕ :=
  GeneralPaperSourceCrossingStreamRates.reservation model W m k+sourceProfile W m k

def reservationCertificate (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    Certificate (fun x => reservation (GeneralPaperFastRationalMajorant.model C d) (W x) x.m x.k) := by
  have hOld := (GeneralPaperSourceCrossingStreamRates.reservationCertificate C d W hW).bound
  have hInput := (certificate W hW).bound
  refine ⟨_,_,_,by unfold reservation; source_space⟩

theorem reservation_degrees (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    ((reservationCertificate C d W hW).fields,(reservationCertificate C d W hW).symbols,
      (reservationCertificate C d W hW).accuracy)=(3,0,4) := rfl

theorem reservation_scaling (model : RationalCostModel) (m k : ℕ) :
    GeneralPaperReferenceScaling.Scale (fun W => reservation model W m k) := by
  have ho := GeneralPaperSourceCrossingStreamRates.reservation_scaling model m k
  have hp := scaling m (GeneralPaperProxyParameters.prepare m k).K (GeneralPaperProxyParameters.prepare m k).S (GeneralPaperSourceRayStorageWidth.width m k)
  unfold reservation sourceProfile
  fun_prop

theorem reservation_mono (actual upper : RationalCostModel) (h : ∀ n,actual.rat n≤upper.rat n) (W m k : ℕ) :
    reservation actual W m k≤reservation upper W m k :=
  Nat.add_le_add_right (GeneralPaperSourceCrossingStreamRates.reservation_mono actual upper h W m k) _

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

end Blotto.GeneralPaperSourceAffineInputRates
