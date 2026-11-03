import Blotto.GeneralPaperRetainedInputsReturnStorage

/-! Complete grid/input parent ownership and native metadata fit
(2,0,2), including full table/grid/parameter/matrix returns. SUM with all
previous packing/controller/source reserves preserves (3,0,4). -/
namespace Blotto.GeneralPaperSourceInitializerReturnStorageRates
open GeneralPaperSourceWordGrowth GeneralPaperSourceSoftBounds GeneralPaperSourceRateAlgebra
open GeneralPaperConstructedWordGrowth GeneralPaperCompilerReferenceGrowth
set_option autoImplicit false
set_option maxHeartbeats 7000000
set_option maxRecDepth 8192

def tableProfile (W m k : ℕ) : ℕ := GeneralPaperEncodedBasisStorage.arrayProfile W m
  (GeneralPaperEncodedBasisStorage.arrayProfile W (GeneralPaperProxyParameters.prepare m k).K
    (GeneralPaperInitializerTableStorage.pairProfile W (GeneralPaperSourceInitializerTableStorageRates.operandWidth m k)))
def gridProfile (W m k : ℕ) : ℕ := GeneralPaperEncodedBasisStorage.arrayProfile W (m*((GeneralPaperProxyParameters.prepare m k).K-1))
  (GeneralPaperSourceBasisGridPackingStorageRates.operandWidth m k)
def matrixProfile (W m k : ℕ) : ℕ := GeneralPaperEncodedScoreMatrixStorage.matrixProfile W m (GeneralPaperProxyParameters.prepare m k).K
  (GeneralPaperProxyParameters.prepare m k).S (GeneralPaperSourceScoreHeights.anchorHeight m k)
def storedPrice (model : RationalCostModel) (W m k : ℕ) : ℕ :=
  let R := GeneralPaperSourceInitializerTableStorageRates.operandWidth m k
  256*m*(GeneralPaperProxyParameters.prepare m k).K*(R+1)*(W+model.rat R)+88*(m+1)*((GeneralPaperProxyParameters.prepare m k).K+1)*W
def packedPrice (model : RationalCostModel) (W m k : ℕ) : ℕ := GeneralPaperBasisGridPackingPrice.profile m (GeneralPaperProxyParameters.prepare m k).K W
  (model.rat (1+binaryWordWidth (m*((GeneralPaperProxyParameters.prepare m k).K-1)+1)))
  (model.rat (GeneralPaperSourceBasisGridPackingStorageRates.operandWidth m k))
def controlPrice (model : RationalCostModel) (W m k : ℕ) : ℕ := GeneralPaperInitializerControlStorage.price model W
  (GeneralPaperSourceInitializerControlStorageRates.operandWidth m k)
def gridPrice (model : RationalCostModel) (W m k : ℕ) : ℕ := storedPrice model W m k+packedPrice model W m k+16*W
def inputPrice (model : RationalCostModel) (W m k : ℕ) : ℕ := controlPrice model W m k+gridPrice model W m k+64*W
def sourceProfile (model : RationalCostModel) (W m k : ℕ) : ℕ :=
  GeneralPaperInitializerGridReturnStorage.profile W (tableProfile W m k) (gridProfile W m k)
    (GeneralPaperSourceBasisGridPackingStorageRates.operandWidth m k) (GeneralPaperSourceInitializerTableStorageRates.operandWidth m k)
    (storedPrice model W m k) (packedPrice model W m k)+
    GeneralPaperRetainedInputsReturnStorage.profile W (GeneralPaperSourceInitializerControlStorageRates.sourceProfile model W m k)
      (gridProfile W m k) (matrixProfile W m k) (controlPrice model W m k) (gridPrice model W m k)

theorem source_scaling (model : RationalCostModel) (m k : ℕ) : GeneralPaperReferenceScaling.Scale (fun W => sourceProfile model W m k) := by
  have hControl := GeneralPaperSourceInitializerControlStorageRates.source_scaling model m k
  unfold sourceProfile tableProfile gridProfile
    matrixProfile gridPrice storedPrice
    packedPrice controlPrice GeneralPaperBasisGridPackingPrice.profile
    GeneralPaperEncodedBasisStorage.arrayProfile GeneralPaperEncodedScoreMatrixStorage.matrixProfile GeneralPaperInitializerControlStorage.price
    GeneralPaperInitializerGridReturnStorage.profile GeneralPaperInitializerTableStorage.pairProfile GeneralPaperRetainedInputsReturnStorage.profile
    GeneralPaperEncodedScoreMatrixStorage.fieldProfile GeneralPaperInitializerGridReturnStorage.metadataCap GeneralPaperRetainedInputsReturnStorage.metadataCap
    GeneralPaperEncodedScoreMatrixStorage.entryProfile GeneralPaperEncodedScalarStorage.natBits GeneralPaperSourceInitializerTableStorageRates.operandWidth
    GeneralPaperSourceBasisGridPackingStorageRates.operandWidth GeneralPaperSourceInitializerControlStorageRates.operandWidth
  dsimp only
  fun_prop

theorem source_model_mono (actual upper : RationalCostModel) (h : ∀ n,actual.rat n≤upper.rat n) (W m k : ℕ) :
    sourceProfile actual W m k≤sourceProfile upper W m k := by
  have hControl := GeneralPaperSourceInitializerControlStorageRates.source_model_mono actual upper h W m k
  unfold sourceProfile tableProfile gridProfile
    matrixProfile gridPrice storedPrice
    packedPrice controlPrice GeneralPaperBasisGridPackingPrice.profile
    GeneralPaperEncodedBasisStorage.arrayProfile GeneralPaperEncodedScoreMatrixStorage.matrixProfile GeneralPaperInitializerControlStorage.price
    GeneralPaperInitializerGridReturnStorage.profile GeneralPaperInitializerTableStorage.pairProfile GeneralPaperRetainedInputsReturnStorage.profile
    GeneralPaperEncodedScoreMatrixStorage.fieldProfile GeneralPaperInitializerGridReturnStorage.metadataCap GeneralPaperRetainedInputsReturnStorage.metadataCap
    GeneralPaperEncodedScoreMatrixStorage.entryProfile GeneralPaperEncodedScalarStorage.natBits GeneralPaperSourceInitializerTableStorageRates.operandWidth
    GeneralPaperSourceBasisGridPackingStorageRates.operandWidth GeneralPaperSourceInitializerControlStorageRates.operandWidth
  dsimp only
  gcongr <;> first | exact hControl | exact h _

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
  have hControl := (GeneralPaperSourceInitializerControlStorageRates.certificate C d W hW).bound
  refine ⟨_,_,_,by
    unfold sourceProfile tableProfile gridProfile
      matrixProfile gridPrice storedPrice
      packedPrice controlPrice GeneralPaperBasisGridPackingPrice.profile
      GeneralPaperEncodedBasisStorage.arrayProfile GeneralPaperEncodedScoreMatrixStorage.matrixProfile GeneralPaperInitializerControlStorage.price
      GeneralPaperInitializerGridReturnStorage.profile GeneralPaperInitializerTableStorage.pairProfile GeneralPaperRetainedInputsReturnStorage.profile
      GeneralPaperEncodedScoreMatrixStorage.fieldProfile GeneralPaperInitializerGridReturnStorage.metadataCap GeneralPaperRetainedInputsReturnStorage.metadataCap
      GeneralPaperEncodedScoreMatrixStorage.entryProfile GeneralPaperEncodedScalarStorage.natBits GeneralPaperSourceInitializerTableStorageRates.operandWidth
      GeneralPaperSourceBasisGridPackingStorageRates.operandWidth GeneralPaperSourceInitializerControlStorageRates.operandWidth
    dsimp only [GeneralPaperFastRationalMajorant.model]
    source_space⟩

theorem degrees (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    ((certificate C d W hW).fields,(certificate C d W hW).symbols,(certificate C d W hW).accuracy)=(2,0,2) := rfl

def reservation (model : RationalCostModel) (W m k : ℕ) : ℕ := GeneralPaperSourceBasisGridPackingStorageRates.reservation model W m k+sourceProfile model W m k
def reservationCertificate (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    Certificate (fun x => reservation (GeneralPaperFastRationalMajorant.model C d) (W x) x.m x.k) := by
  have hOld := (GeneralPaperSourceBasisGridPackingStorageRates.reservationCertificate C d W hW).bound
  have hNew := (certificate C d W hW).bound
  refine ⟨_,_,_,by unfold reservation; source_space⟩

theorem reservation_degrees (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    ((reservationCertificate C d W hW).fields,(reservationCertificate C d W hW).symbols,(reservationCertificate C d W hW).accuracy)=(3,0,4) := rfl

theorem reservation_scaling (model : RationalCostModel) (m k : ℕ) : GeneralPaperReferenceScaling.Scale (fun W => reservation model W m k) := by
  have hOld := GeneralPaperSourceBasisGridPackingStorageRates.reservation_scaling model m k
  have hNew := source_scaling model m k
  unfold reservation
  fun_prop

theorem reservation_mono (actual upper : RationalCostModel) (h : ∀ n,actual.rat n≤upper.rat n) (W m k : ℕ) :
    reservation actual W m k≤reservation upper W m k :=
  Nat.add_le_add (GeneralPaperSourceBasisGridPackingStorageRates.reservation_mono actual upper h W m k) (source_model_mono actual upper h W m k)

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

end Blotto.GeneralPaperSourceInitializerReturnStorageRates
