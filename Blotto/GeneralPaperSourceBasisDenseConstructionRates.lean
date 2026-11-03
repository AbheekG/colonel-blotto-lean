import Blotto.GeneralPaperBasisDenseConstructionStorage

/-! Complete native original sparse-to-dense construction has source
degree (2,0,1). Coordinate arithmetic/map, zero fill/scatter and full dense
row/RHS/native-annotation returns coexist. Summing with all previous actual
row-constructor/endpoint/high/data reserves preserves (3,0,4). -/
namespace Blotto.GeneralPaperSourceBasisDenseConstructionRates
open GeneralPaperSourceWordGrowth GeneralPaperSourceSoftBounds GeneralPaperSourceRateAlgebra
open GeneralPaperConstructedWordGrowth GeneralPaperCompilerReferenceGrowth
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192

def profile (model : RationalCostModel) (W _T m K _S _R : ℕ) : ℕ :=
  GeneralPaperBasisDenseConstructionStorage.profile model W m K

theorem height_mono (model : RationalCostModel) (W T m K S R H : ℕ) (_hR : R≤H) : profile model W T m K S R≤profile model W T m K S H := le_rfl

theorem scaling (model : RationalCostModel) (T m K S R : ℕ) :
    GeneralPaperReferenceScaling.Scale (fun W => profile model W T m K S R) := by
  unfold profile GeneralPaperBasisDenseConstructionStorage.profile GeneralPaperBasisCoordinateStorage.profile
    GeneralPaperBasisDenseConstructionStorage.metadataCap GeneralPaperBasisScatterStorage.profile GeneralPaperEncodedBasisStorage.rowProfile
    GeneralPaperStaticRowResidualStorage.rowProfile GeneralPaperBasisCoordinateStorage.callbackPrice GeneralPaperBasisCoordinateStorage.callbackProfile
    GeneralPaperBasisCoordinateStorage.metadataCap GeneralPaperBasisDenseConstructionStorage.annotation GeneralPaperBasisDenseConstructionStorage.price
    GeneralPaperBasisScatterStorage.callerCap GeneralPaperBasisScatterStorage.frameProfile GeneralPaperNativePayloadFillStorage.profile
    GeneralPaperPricedPayloadStreamStorage.filterProfile GeneralPaperBasisCoordinateStorage.packedTermProfile GeneralPaperBasisCoordinateStorage.price
    GeneralPaperBasisCoordinateStorage.scalarProfile GeneralPaperBasisScatterStorage.metadataCap GeneralPaperBasisScatterStorage.vectorProfile
    GeneralPaperNativePayloadFillStorage.frameProfile GeneralPaperPricedPayloadStreamStorage.filterFrameProfile GeneralPaperPricedPayloadStreamStorage.listProfile
    GeneralPaperStaticRowResidualStorage.termProfile GeneralPaperBasisCoordinateStorage.scalarCap GeneralPaperBasisScatterStorage.stepCap
    GeneralPaperEncodedBasisStorage.arrayProfile GeneralPaperEncodedScalarStorage.natBits GeneralPaperNativePayloadFillStorage.metadataCap
    GeneralPaperPricedPayloadStreamStorage.filterCap GeneralPaperPricedPayloadStreamStorage.optionProfile GeneralPaperBasisCoordinateStorage.scalarPrice
    GeneralPaperNativePayloadFillStorage.workCap GeneralPaperPricedPayloadStreamStorage.filterWork
  fun_prop

theorem model_mono (actual upper : RationalCostModel) (h : ∀ n,actual.rat n≤upper.rat n) (W T m K S R : ℕ) :
    profile actual W T m K S R≤profile upper W T m K S R := by
  unfold profile GeneralPaperBasisDenseConstructionStorage.profile GeneralPaperBasisCoordinateStorage.profile
    GeneralPaperBasisDenseConstructionStorage.metadataCap GeneralPaperBasisScatterStorage.profile GeneralPaperEncodedBasisStorage.rowProfile
    GeneralPaperStaticRowResidualStorage.rowProfile GeneralPaperBasisCoordinateStorage.callbackPrice GeneralPaperBasisCoordinateStorage.callbackProfile
    GeneralPaperBasisCoordinateStorage.metadataCap GeneralPaperBasisDenseConstructionStorage.annotation GeneralPaperBasisDenseConstructionStorage.price
    GeneralPaperBasisScatterStorage.callerCap GeneralPaperBasisScatterStorage.frameProfile GeneralPaperNativePayloadFillStorage.profile
    GeneralPaperPricedPayloadStreamStorage.filterProfile GeneralPaperBasisCoordinateStorage.packedTermProfile GeneralPaperBasisCoordinateStorage.price
    GeneralPaperBasisCoordinateStorage.scalarProfile GeneralPaperBasisScatterStorage.metadataCap GeneralPaperBasisScatterStorage.vectorProfile
    GeneralPaperNativePayloadFillStorage.frameProfile GeneralPaperPricedPayloadStreamStorage.filterFrameProfile GeneralPaperPricedPayloadStreamStorage.listProfile
    GeneralPaperStaticRowResidualStorage.termProfile GeneralPaperBasisCoordinateStorage.scalarCap GeneralPaperBasisScatterStorage.stepCap
    GeneralPaperEncodedBasisStorage.arrayProfile GeneralPaperEncodedScalarStorage.natBits GeneralPaperNativePayloadFillStorage.metadataCap
    GeneralPaperPricedPayloadStreamStorage.filterCap GeneralPaperPricedPayloadStreamStorage.optionProfile GeneralPaperBasisCoordinateStorage.scalarPrice
    GeneralPaperNativePayloadFillStorage.workCap GeneralPaperPricedPayloadStreamStorage.filterWork
  gcongr <;> exact h _

def sourceProfile (model : RationalCostModel) (W m k : ℕ) : ℕ :=
  profile model W (GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet m k).lambda k).rows m (GeneralPaperProxyParameters.prepare m k).K (GeneralPaperProxyParameters.prepare m k).S
    (GeneralPaperSourceRayStorageWidth.width m k)

def certificate (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    Certificate (fun x => sourceProfile (GeneralPaperFastRationalMajorant.model C d) (W x) x.m x.k) := by
  have hr : Rated W 0 0 0 := poly (poly_tight W hW)
  have hs := of_tight hW
  have hRows := GeneralPaperSourceStaticConstructionRates.sharp_rows
  have hR := GeneralPaperSourceSharpOperandRates.ray_width
  have hsR := GeneralPaperSourceRayStorageRates.width_small
  refine ⟨_,_,_,by
    unfold sourceProfile profile GeneralPaperBasisDenseConstructionStorage.profile
      GeneralPaperBasisCoordinateStorage.profile GeneralPaperBasisDenseConstructionStorage.metadataCap GeneralPaperBasisScatterStorage.profile
      GeneralPaperEncodedBasisStorage.rowProfile GeneralPaperStaticRowResidualStorage.rowProfile GeneralPaperBasisCoordinateStorage.callbackPrice
      GeneralPaperBasisCoordinateStorage.callbackProfile GeneralPaperBasisCoordinateStorage.metadataCap GeneralPaperBasisDenseConstructionStorage.annotation
      GeneralPaperBasisDenseConstructionStorage.price GeneralPaperBasisScatterStorage.callerCap GeneralPaperBasisScatterStorage.frameProfile
      GeneralPaperNativePayloadFillStorage.profile GeneralPaperPricedPayloadStreamStorage.filterProfile GeneralPaperBasisCoordinateStorage.packedTermProfile
      GeneralPaperBasisCoordinateStorage.price GeneralPaperBasisCoordinateStorage.scalarProfile GeneralPaperBasisScatterStorage.metadataCap
      GeneralPaperBasisScatterStorage.vectorProfile GeneralPaperNativePayloadFillStorage.frameProfile GeneralPaperPricedPayloadStreamStorage.filterFrameProfile
      GeneralPaperPricedPayloadStreamStorage.listProfile GeneralPaperStaticRowResidualStorage.termProfile GeneralPaperBasisCoordinateStorage.scalarCap
      GeneralPaperBasisScatterStorage.stepCap GeneralPaperEncodedBasisStorage.arrayProfile GeneralPaperEncodedScalarStorage.natBits
      GeneralPaperNativePayloadFillStorage.metadataCap GeneralPaperPricedPayloadStreamStorage.filterCap GeneralPaperPricedPayloadStreamStorage.optionProfile
      GeneralPaperBasisCoordinateStorage.scalarPrice GeneralPaperNativePayloadFillStorage.workCap GeneralPaperPricedPayloadStreamStorage.filterWork
    dsimp only [GeneralPaperFastRationalMajorant.model]
    source_space⟩

theorem degrees (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    ((certificate C d W hW).fields,(certificate C d W hW).symbols,(certificate C d W hW).accuracy)=(2,0,1) := rfl

theorem actual_rate {actual : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth actual C d)
    (W : Input → ℕ) (hW : Tight W) : Rated (fun x => sourceProfile actual (W x) x.m x.k) 2 0 1 :=
  GeneralPaperSourceSoftBounds.dominated (certificate C d W hW).bound
    (fun x => model_mono actual (GeneralPaperFastRationalMajorant.model C d) (GeneralPaperFastRationalMajorant.dominates hg) (W x) _ _ _ _ _)

def reservation (model : RationalCostModel) (W m k : ℕ) : ℕ :=
  GeneralPaperSourceBlockerRowConstructionRates.reservation model W m k+sourceProfile model W m k

def reservationCertificate (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    Certificate (fun x => reservation (GeneralPaperFastRationalMajorant.model C d) (W x) x.m x.k) := by
  have hOld := (GeneralPaperSourceBlockerRowConstructionRates.reservationCertificate C d W hW).bound
  have hGeneration := (certificate C d W hW).bound
  refine ⟨_,_,_,by unfold reservation; source_space⟩

theorem reservation_degrees (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    ((reservationCertificate C d W hW).fields,(reservationCertificate C d W hW).symbols,
      (reservationCertificate C d W hW).accuracy)=(3,0,4) := rfl

theorem reservation_scaling (model : RationalCostModel) (m k : ℕ) :
    GeneralPaperReferenceScaling.Scale (fun W => reservation model W m k) := by
  have ho := GeneralPaperSourceBlockerRowConstructionRates.reservation_scaling model m k
  have hp := scaling model (GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet m k).lambda k).rows m (GeneralPaperProxyParameters.prepare m k).K (GeneralPaperProxyParameters.prepare m k).S (GeneralPaperSourceRayStorageWidth.width m k)
  unfold reservation sourceProfile
  fun_prop

theorem reservation_mono (actual upper : RationalCostModel) (h : ∀ n,actual.rat n≤upper.rat n) (W m k : ℕ) :
    reservation actual W m k≤reservation upper W m k :=
  Nat.add_le_add (GeneralPaperSourceBlockerRowConstructionRates.reservation_mono actual upper h W m k) (model_mono actual upper h W _ _ _ _ _)

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

end Blotto.GeneralPaperSourceBasisDenseConstructionRates
