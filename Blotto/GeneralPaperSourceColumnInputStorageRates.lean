import Blotto.GeneralPaperColumnInputStorage

/-! Full source-row ownership and literal native field materialization
fit paper space (3,0,4). SUM with every prior representative-sort/anchor/
normalization/strict/source/endpoint reserve preserves the same rate. -/
namespace Blotto.GeneralPaperSourceColumnInputStorageRates
open GeneralPaperSourceWordGrowth GeneralPaperSourceSoftBounds GeneralPaperSourceRateAlgebra
open GeneralPaperConstructedWordGrowth GeneralPaperCompilerReferenceGrowth
set_option autoImplicit false
set_option maxHeartbeats 7000000
set_option maxRecDepth 16384

def operandWidth (m k : ℕ) : ℕ := 1+2*GeneralPaperSourceScoreHeights.anchorHeight m k
def sourceProfile (_model : RationalCostModel) (W m k : ℕ) : ℕ := GeneralPaperColumnInputStorage.profile W
  (GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet m k).lambda k).rows m (operandWidth m k)

theorem source_scaling (model : RationalCostModel) (m k : ℕ) : GeneralPaperReferenceScaling.Scale (fun W => sourceProfile model W m k) := by
  unfold sourceProfile operandWidth GeneralPaperColumnInputStorage.profile
    GeneralPaperColumnInputStorage.metadataCap GeneralPaperColumnInputStorage.scalarProfile GeneralPaperEnclosingSourceOwners.rowsProfile
    GeneralPaperNativePayloadFillStorage.profile GeneralPaperColumnInputStorage.price GeneralPaperColumnInputStorage.scalarCap
    GeneralPaperEncodedBasisStorage.arrayProfile GeneralPaperNativePayloadFillStorage.frameProfile GeneralPaperEncodedScalarStorage.natBits
    GeneralPaperNativePayloadFillStorage.metadataCap GeneralPaperNativePayloadFillStorage.workCap
  fun_prop

theorem source_model_mono (actual upper : RationalCostModel) (_h : ∀ n,actual.rat n≤upper.rat n) (W m k : ℕ) :
    sourceProfile actual W m k≤sourceProfile upper W m k := le_rfl

def certificate (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    Certificate (fun x => sourceProfile (GeneralPaperFastRationalMajorant.model C d) (W x) x.m x.k) := by
  have hr : Rated W 0 0 0 := poly (poly_tight W hW)
  have hs := of_tight hW
  have hA := GeneralPaperSourceSharpOperandRates.anchor_height
  have hsA := GeneralPaperScoreStorageRates.anchor_small
  have hRows := GeneralPaperSourceStaticConstructionRates.sharp_rows
  refine ⟨_,_,_,by
    unfold sourceProfile operandWidth GeneralPaperColumnInputStorage.profile
      GeneralPaperColumnInputStorage.metadataCap GeneralPaperColumnInputStorage.scalarProfile GeneralPaperEnclosingSourceOwners.rowsProfile
      GeneralPaperNativePayloadFillStorage.profile GeneralPaperColumnInputStorage.price GeneralPaperColumnInputStorage.scalarCap
      GeneralPaperEncodedBasisStorage.arrayProfile GeneralPaperNativePayloadFillStorage.frameProfile GeneralPaperEncodedScalarStorage.natBits
      GeneralPaperNativePayloadFillStorage.metadataCap GeneralPaperNativePayloadFillStorage.workCap
    source_space⟩

theorem degrees (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    ((certificate C d W hW).fields,(certificate C d W hW).symbols,(certificate C d W hW).accuracy)=(3,0,4) := rfl

def reservation (model : RationalCostModel) (W m k Qv : ℕ) : ℕ := GeneralPaperSourceRepresentativeSortStorageRates.reservation model W m k Qv+sourceProfile model W m k

def reservationCertificate (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    Certificate (fun x => reservation (GeneralPaperFastRationalMajorant.model C d) (W x) x.m x.k x.Qv) := by
  refine ⟨3,0,4,?_⟩
  exact GeneralPaperSourceRateAlgebra.add _ _ 3 0 4 3 0 4
    (GeneralPaperSourceRepresentativeSortStorageRates.reservationCertificate C d W hW).bound (certificate C d W hW).bound

theorem reservation_degrees (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    ((reservationCertificate C d W hW).fields,(reservationCertificate C d W hW).symbols,(reservationCertificate C d W hW).accuracy)=(3,0,4) := rfl

theorem reservation_scaling (model : RationalCostModel) (m k Qv : ℕ) : GeneralPaperReferenceScaling.Scale (fun W => reservation model W m k Qv) := by
  have hOld := GeneralPaperSourceRepresentativeSortStorageRates.reservation_scaling model m k Qv
  have hNew := source_scaling model m k
  unfold reservation
  fun_prop

theorem reservation_mono (actual upper : RationalCostModel) (h : ∀ n,actual.rat n≤upper.rat n) (W m k Qv : ℕ) :
    reservation actual W m k Qv≤reservation upper W m k Qv :=
  Nat.add_le_add (GeneralPaperSourceRepresentativeSortStorageRates.reservation_mono actual upper h W m k Qv) (source_model_mono actual upper h W m k)

theorem actual_reservation_rate {actual : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth actual C d)
    (W : Input → ℕ) (hW : Tight W) : Rated (fun x => reservation actual (W x) x.m x.k x.Qv) 3 0 4 :=
  GeneralPaperSourceSoftBounds.dominated (reservationCertificate C d W hW).bound
    (fun x => reservation_mono actual (GeneralPaperFastRationalMajorant.model C d) (GeneralPaperFastRationalMajorant.dominates hg) (W x) x.m x.k x.Qv)

theorem reservation_at_one_small (C d : ℕ) : Small (fun x => reservation (GeneralPaperFastRationalMajorant.model C d) 1 x.m x.k x.Qv) := by
  apply GeneralPaperSourceRowsStorageRates.soft_small (reservationCertificate C d (fun _ => 1) (tight_constant 1)).bound
  unfold monomial GeneralPaperNativeSourceRates.fields GeneralPaperNativeSourceRates.symbols GeneralPaperNativeSourceRates.accuracy
  fun_prop

theorem actual_common_word {actual : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth actual C d) :
    ∃ A e : ℕ,∀ x,reservation actual (GeneralPaperCompilerReference.width C d x) x.m x.k x.Qv≤A*(x.m+1)^3*2^(4*x.k)*(logSize x)^e := by
  rcases actual_reservation_rate hg (GeneralPaperCompilerReference.width C d) (width_tight C d) with ⟨A,e,hA⟩
  refine ⟨A,e,?_⟩
  intro x
  have he : (GeneralPaperNativeSourceRates.accuracy x)^4=2^(4*x.k) := by simp only [GeneralPaperNativeSourceRates.accuracy,←pow_mul,Nat.mul_comm x.k 4]
  simpa only [monomial,pow_zero,Nat.mul_one,GeneralPaperNativeSourceRates.fields,he,Nat.mul_assoc] using hA x

end Blotto.GeneralPaperSourceColumnInputStorageRates
