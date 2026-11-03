import Blotto.GeneralPaperBasisGridPackingStorage

/-! Complete native grid packing, full conservative write frames and
all enumeration/coordinate/entry/zero-fill/parent lifetimes fit (3,0,3).
SUM with previous stored-table/scalar/controller/source reserves keeps
the paper common-word space degree (3,0,4). -/
namespace Blotto.GeneralPaperSourceBasisGridPackingStorageRates
open GeneralPaperSourceWordGrowth GeneralPaperSourceSoftBounds GeneralPaperSourceRateAlgebra
open GeneralPaperConstructedWordGrowth GeneralPaperCompilerReferenceGrowth
set_option autoImplicit false
set_option maxHeartbeats 7000000
set_option maxRecDepth 8192

def operandWidth (m k : ℕ) : ℕ := 1+GeneralPaperSourceRayStorageWidth.gridWord m k
def sourceProfile (model : RationalCostModel) (W m k : ℕ) : ℕ :=
  GeneralPaperBasisGridPackingStorage.profile model W m (GeneralPaperProxyParameters.prepare m k).K (operandWidth m k)

theorem source_scaling (model : RationalCostModel) (m k : ℕ) : GeneralPaperReferenceScaling.Scale (fun W => sourceProfile model W m k) := by
  unfold sourceProfile GeneralPaperBasisGridPackingStorage.profile GeneralPaperBasisGridEntryStorage.profile
    GeneralPaperBasisGridPackingStorage.metadataCap GeneralPaperBasisGridWriteStorage.profile GeneralPaperNativePayloadFillStorage.profile
    GeneralPaperStaticVariableConstructionStorage.profile GeneralPaperBasisGridEntryStorage.callbackProfile GeneralPaperBasisGridEntryStorage.metadataCap
    GeneralPaperBasisGridPackingStorage.price GeneralPaperBasisGridWriteStorage.frameProfile GeneralPaperFinRangeStorage.profile
    GeneralPaperNativePayloadFillStorage.frameProfile GeneralPaperPricedPayloadStreamStorage.flatProfile GeneralPaperStaticVariableConstructionStorage.callerCap
    GeneralPaperStaticVariableConstructionStorage.innerProfile GeneralPaperBasisCoordinateStorage.scalarProfile GeneralPaperBasisGridEntryStorage.callbackCap
    GeneralPaperBasisGridEntryStorage.packedProfile GeneralPaperBasisGridEntryStorage.price GeneralPaperBasisGridWriteStorage.metadataCap
    GeneralPaperEncodedBasisStorage.arrayProfile GeneralPaperNativePayloadFillStorage.metadataCap GeneralPaperPricedPayloadStreamStorage.filterProfile
    GeneralPaperPricedPayloadStreamStorage.flatFrameProfile GeneralPaperStaticVariableConstructionStorage.innerCap GeneralPaperStaticVariableConstructionStorage.price
    GeneralPaperStaticVariableConstructionStorage.variableProfile GeneralPaperBasisCoordinateStorage.scalarCap GeneralPaperBasisGridEntryStorage.callbackPrice
    GeneralPaperBasisGridWriteStorage.price GeneralPaperNativePayloadFillStorage.workCap GeneralPaperPricedPayloadStreamStorage.filterFrameProfile
    GeneralPaperPricedPayloadStreamStorage.flatCap GeneralPaperPricedPayloadStreamStorage.listProfile GeneralPaperStaticVariableConstructionStorage.rowPrice
    GeneralPaperBasisCoordinateStorage.scalarPrice GeneralPaperEncodedScalarStorage.natBits GeneralPaperPricedPayloadStreamStorage.filterCap
    GeneralPaperPricedPayloadStreamStorage.flatWork GeneralPaperPricedPayloadStreamStorage.optionProfile GeneralPaperPricedPayloadStreamStorage.filterWork
  dsimp only
  fun_prop

theorem source_model_mono (actual upper : RationalCostModel) (h : ∀ n,actual.rat n≤upper.rat n) (W m k : ℕ) :
    sourceProfile actual W m k≤sourceProfile upper W m k := by
  unfold sourceProfile GeneralPaperBasisGridPackingStorage.profile GeneralPaperBasisGridEntryStorage.profile
    GeneralPaperBasisGridPackingStorage.metadataCap GeneralPaperBasisGridWriteStorage.profile GeneralPaperNativePayloadFillStorage.profile
    GeneralPaperStaticVariableConstructionStorage.profile GeneralPaperBasisGridEntryStorage.callbackProfile GeneralPaperBasisGridEntryStorage.metadataCap
    GeneralPaperBasisGridPackingStorage.price GeneralPaperBasisGridWriteStorage.frameProfile GeneralPaperFinRangeStorage.profile
    GeneralPaperNativePayloadFillStorage.frameProfile GeneralPaperPricedPayloadStreamStorage.flatProfile GeneralPaperStaticVariableConstructionStorage.callerCap
    GeneralPaperStaticVariableConstructionStorage.innerProfile GeneralPaperBasisCoordinateStorage.scalarProfile GeneralPaperBasisGridEntryStorage.callbackCap
    GeneralPaperBasisGridEntryStorage.packedProfile GeneralPaperBasisGridEntryStorage.price GeneralPaperBasisGridWriteStorage.metadataCap
    GeneralPaperEncodedBasisStorage.arrayProfile GeneralPaperNativePayloadFillStorage.metadataCap GeneralPaperPricedPayloadStreamStorage.filterProfile
    GeneralPaperPricedPayloadStreamStorage.flatFrameProfile GeneralPaperStaticVariableConstructionStorage.innerCap GeneralPaperStaticVariableConstructionStorage.price
    GeneralPaperStaticVariableConstructionStorage.variableProfile GeneralPaperBasisCoordinateStorage.scalarCap GeneralPaperBasisGridEntryStorage.callbackPrice
    GeneralPaperBasisGridWriteStorage.price GeneralPaperNativePayloadFillStorage.workCap GeneralPaperPricedPayloadStreamStorage.filterFrameProfile
    GeneralPaperPricedPayloadStreamStorage.flatCap GeneralPaperPricedPayloadStreamStorage.listProfile GeneralPaperStaticVariableConstructionStorage.rowPrice
    GeneralPaperBasisCoordinateStorage.scalarPrice GeneralPaperEncodedScalarStorage.natBits GeneralPaperPricedPayloadStreamStorage.filterCap
    GeneralPaperPricedPayloadStreamStorage.flatWork GeneralPaperPricedPayloadStreamStorage.optionProfile GeneralPaperPricedPayloadStreamStorage.filterWork
  dsimp only
  gcongr <;> exact h _

def certificate (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    Certificate (fun x => sourceProfile (GeneralPaperFastRationalMajorant.model C d) (W x) x.m x.k) := by
  have hr : Rated W 0 0 0 := poly (poly_tight W hW)
  have hs := of_tight hW
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
  have hR : Rated (fun x => operandWidth x.m x.k) 1 0 1 := by unfold operandWidth; source_space
  have hsR : Small (fun x => operandWidth x.m x.k) := by unfold operandWidth; fun_prop
  refine ⟨_,_,_,by
    unfold sourceProfile GeneralPaperBasisGridPackingStorage.profile GeneralPaperBasisGridEntryStorage.profile
      GeneralPaperBasisGridPackingStorage.metadataCap GeneralPaperBasisGridWriteStorage.profile GeneralPaperNativePayloadFillStorage.profile
      GeneralPaperStaticVariableConstructionStorage.profile GeneralPaperBasisGridEntryStorage.callbackProfile GeneralPaperBasisGridEntryStorage.metadataCap
      GeneralPaperBasisGridPackingStorage.price GeneralPaperBasisGridWriteStorage.frameProfile GeneralPaperFinRangeStorage.profile
      GeneralPaperNativePayloadFillStorage.frameProfile GeneralPaperPricedPayloadStreamStorage.flatProfile GeneralPaperStaticVariableConstructionStorage.callerCap
      GeneralPaperStaticVariableConstructionStorage.innerProfile GeneralPaperBasisCoordinateStorage.scalarProfile GeneralPaperBasisGridEntryStorage.callbackCap
      GeneralPaperBasisGridEntryStorage.packedProfile GeneralPaperBasisGridEntryStorage.price GeneralPaperBasisGridWriteStorage.metadataCap
      GeneralPaperEncodedBasisStorage.arrayProfile GeneralPaperNativePayloadFillStorage.metadataCap GeneralPaperPricedPayloadStreamStorage.filterProfile
      GeneralPaperPricedPayloadStreamStorage.flatFrameProfile GeneralPaperStaticVariableConstructionStorage.innerCap GeneralPaperStaticVariableConstructionStorage.price
      GeneralPaperStaticVariableConstructionStorage.variableProfile GeneralPaperBasisCoordinateStorage.scalarCap GeneralPaperBasisGridEntryStorage.callbackPrice
      GeneralPaperBasisGridWriteStorage.price GeneralPaperNativePayloadFillStorage.workCap GeneralPaperPricedPayloadStreamStorage.filterFrameProfile
      GeneralPaperPricedPayloadStreamStorage.flatCap GeneralPaperPricedPayloadStreamStorage.listProfile GeneralPaperStaticVariableConstructionStorage.rowPrice
      GeneralPaperBasisCoordinateStorage.scalarPrice GeneralPaperEncodedScalarStorage.natBits GeneralPaperPricedPayloadStreamStorage.filterCap
      GeneralPaperPricedPayloadStreamStorage.flatWork GeneralPaperPricedPayloadStreamStorage.optionProfile GeneralPaperPricedPayloadStreamStorage.filterWork
    dsimp only [GeneralPaperFastRationalMajorant.model]
    source_space⟩

theorem degrees (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    ((certificate C d W hW).fields,(certificate C d W hW).symbols,(certificate C d W hW).accuracy)=(3,0,3) := rfl

def reservation (model : RationalCostModel) (W m k : ℕ) : ℕ := GeneralPaperSourceInitializerTableStorageRates.reservation model W m k+sourceProfile model W m k
def reservationCertificate (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    Certificate (fun x => reservation (GeneralPaperFastRationalMajorant.model C d) (W x) x.m x.k) := by
  have hOld := (GeneralPaperSourceInitializerTableStorageRates.reservationCertificate C d W hW).bound
  have hNew := (certificate C d W hW).bound
  refine ⟨_,_,_,by unfold reservation; source_space⟩

theorem reservation_degrees (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    ((reservationCertificate C d W hW).fields,(reservationCertificate C d W hW).symbols,(reservationCertificate C d W hW).accuracy)=(3,0,4) := rfl

theorem reservation_scaling (model : RationalCostModel) (m k : ℕ) : GeneralPaperReferenceScaling.Scale (fun W => reservation model W m k) := by
  have hOld := GeneralPaperSourceInitializerTableStorageRates.reservation_scaling model m k
  have hNew := source_scaling model m k
  unfold reservation
  fun_prop

theorem reservation_mono (actual upper : RationalCostModel) (h : ∀ n,actual.rat n≤upper.rat n) (W m k : ℕ) :
    reservation actual W m k≤reservation upper W m k :=
  Nat.add_le_add (GeneralPaperSourceInitializerTableStorageRates.reservation_mono actual upper h W m k) (source_model_mono actual upper h W m k)

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

end Blotto.GeneralPaperSourceBasisGridPackingStorageRates
