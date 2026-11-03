import Blotto.GeneralPaperCrossingSearchStorage

/-! Selected native search caller storage retains source degree (3,0,2)
with one full owner/predicate query reservation. Its native work price is
used only inside encoded counters. Adding search to the prior sort and
resident/basis reservation preserves (3,0,4), before final lifetime joins. -/
namespace Blotto.GeneralPaperSourceSearchStorageRates
open GeneralPaperSourceWordGrowth GeneralPaperSourceSoftBounds GeneralPaperSourceRateAlgebra
open GeneralPaperConstructedWordGrowth GeneralPaperCompilerReferenceGrowth
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

theorem scaling (model : RationalCostModel) (n R : ℕ) (E Q : ℕ → ℕ)
    (hE : GeneralPaperReferenceScaling.Scale E) (hQ : GeneralPaperReferenceScaling.Scale Q) :
    GeneralPaperReferenceScaling.Scale (fun W => GeneralPaperCrossingSearchStorage.profile model W n R (E W) (Q W)) := by
  unfold GeneralPaperCrossingSearchStorage.profile GeneralPaperCrossingSearchStorage.readProfile GeneralPaperCrossingSearchStorage.readCap
    GeneralPaperSelectedSearchStorage.profile GeneralPaperSelectedSearchStorage.metadataCap GeneralPaperSelectedSearchStorage.workCap GeneralPaperSelectedSearchStorage.depth
    GeneralPaperCeilingConstructionStorage.word GeneralPaperRaySearchStorage.coefficient
    GeneralPaperRaySearchStorage.frameProfile GeneralPaperRaySearchStorage.metadataCap GeneralPaperRaySearchStorage.workCap
    GeneralPaperRankMidpointStorage.profile GeneralPaperRankMidpointStorage.argumentHeight GeneralPaperRankMidpointStorage.metadataCap
    GeneralPaperQuotientConstructionStorage.frameCap GeneralPaperQuotientConstructionStorage.localCap GeneralPaperBoundedQuotient.heightBudget GeneralPaperEncodedScalarStorage.natBits
  dsimp only
  fun_prop

theorem model_mono (actual upper : RationalCostModel) (h : ∀ n,actual.rat n≤upper.rat n) (W n R E F Q U : ℕ)
    (hE : E≤F) (hQ : Q≤U) :
    GeneralPaperCrossingSearchStorage.profile actual W n R E Q≤GeneralPaperCrossingSearchStorage.profile upper W n R F U := by
  unfold GeneralPaperCrossingSearchStorage.profile GeneralPaperCrossingSearchStorage.readProfile GeneralPaperCrossingSearchStorage.readCap
    GeneralPaperSelectedSearchStorage.profile GeneralPaperSelectedSearchStorage.metadataCap GeneralPaperSelectedSearchStorage.workCap GeneralPaperSelectedSearchStorage.depth
    GeneralPaperCeilingConstructionStorage.word GeneralPaperRaySearchStorage.coefficient
    GeneralPaperRaySearchStorage.frameProfile GeneralPaperRaySearchStorage.metadataCap GeneralPaperRaySearchStorage.workCap
    GeneralPaperRankMidpointStorage.profile GeneralPaperRankMidpointStorage.argumentHeight GeneralPaperRankMidpointStorage.metadataCap
    GeneralPaperQuotientConstructionStorage.frameCap GeneralPaperQuotientConstructionStorage.localCap GeneralPaperBoundedQuotient.heightBudget GeneralPaperEncodedScalarStorage.natBits
  dsimp only
  gcongr <;> exact h _

def sourceProfile (model : RationalCostModel) (W m k : ℕ) : ℕ :=
  GeneralPaperCrossingSearchStorage.profile model W
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
  have hQuery := (GeneralPaperSourceSharpOwnerRates.certificate C d W hW).bound
  refine ⟨_,_,_,by
    unfold sourceProfile GeneralPaperCrossingSearchStorage.profile GeneralPaperCrossingSearchStorage.readProfile GeneralPaperCrossingSearchStorage.readCap
      GeneralPaperCrossingSearchStorage.nativePrice GeneralPaperSelectedSearchStorage.profile GeneralPaperSelectedSearchStorage.metadataCap
      GeneralPaperSelectedSearchStorage.workCap GeneralPaperSelectedSearchStorage.depth GeneralPaperCeilingConstructionStorage.word
      GeneralPaperRaySearchStorage.coefficient GeneralPaperRaySearchStorage.frameProfile GeneralPaperRaySearchStorage.metadataCap GeneralPaperRaySearchStorage.workCap
      GeneralPaperRankMidpointStorage.profile GeneralPaperRankMidpointStorage.argumentHeight GeneralPaperRankMidpointStorage.metadataCap
      GeneralPaperQuotientConstructionStorage.frameCap GeneralPaperQuotientConstructionStorage.localCap GeneralPaperBoundedQuotient.heightBudget GeneralPaperEncodedScalarStorage.natBits
    dsimp only [GeneralPaperFastRationalMajorant.model]
    source_space⟩

theorem degrees (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    ((certificate C d W hW).fields,(certificate C d W hW).symbols,(certificate C d W hW).accuracy)=(3,0,2) := rfl

theorem actual_rate {actual : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth actual C d)
    (W : Input → ℕ) (hW : Tight W) : Rated (fun x => sourceProfile actual (W x) x.m x.k) 3 0 2 :=
  GeneralPaperSourceSoftBounds.dominated (certificate C d W hW).bound
    (fun x => source_mono actual (GeneralPaperFastRationalMajorant.model C d) (GeneralPaperFastRationalMajorant.dominates hg) (W x) x.m x.k)

def reservation (model : RationalCostModel) (W m k : ℕ) : ℕ :=
  GeneralPaperSourceSortStorageRates.reservation model W m k+sourceProfile model W m k

def reservationCertificate (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    Certificate (fun x => reservation (GeneralPaperFastRationalMajorant.model C d) (W x) x.m x.k) := by
  have hOld := (GeneralPaperSourceSortStorageRates.reservationCertificate C d W hW).bound
  have hSearch := (certificate C d W hW).bound
  refine ⟨_,_,_,by unfold reservation; source_space⟩

theorem reservation_degrees (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    ((reservationCertificate C d W hW).fields,(reservationCertificate C d W hW).symbols,
      (reservationCertificate C d W hW).accuracy)=(3,0,4) := rfl

theorem reservation_scaling (model : RationalCostModel) (m k : ℕ) :
    GeneralPaperReferenceScaling.Scale (fun W => reservation model W m k) := by
  have ho := GeneralPaperSourceSortStorageRates.reservation_scaling model m k
  have hs := source_scaling model m k
  unfold reservation
  fun_prop

theorem reservation_mono (actual upper : RationalCostModel) (h : ∀ n,actual.rat n≤upper.rat n) (W m k : ℕ) :
    reservation actual W m k≤reservation upper W m k :=
  Nat.add_le_add (GeneralPaperSourceSortStorageRates.reservation_mono actual upper h W m k) (source_mono actual upper h W m k)

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

end Blotto.GeneralPaperSourceSearchStorageRates
