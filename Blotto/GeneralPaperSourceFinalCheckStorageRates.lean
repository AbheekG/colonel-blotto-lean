import Blotto.GeneralPaperFinalPolytopeStorage

/-! Both complete final static/strict-score DP feasibility checks fit
degree (3,0,4). Full native Boolean frames, enumeration/row construction,
all active DP phases and caller returns join preceding source reserves. -/
namespace Blotto.GeneralPaperSourceFinalCheckStorageRates
open GeneralPaperSourceWordGrowth GeneralPaperSourceSoftBounds GeneralPaperSourceRateAlgebra
open GeneralPaperConstructedWordGrowth GeneralPaperCompilerReferenceGrowth
set_option autoImplicit false
set_option maxHeartbeats 7000000
set_option maxRecDepth 8192

def operandWidth (m k : ℕ) : ℕ := 64*GeneralPaperSourceRawAffineStorageRates.operandWidth m k
def sourceProfile (model : RationalCostModel) (W m k : ℕ) : ℕ :=
  2*GeneralPaperFinalPolytopeStorage.profile model W
    (GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet m k).lambda k).rows m
    (GeneralPaperProxyParameters.prepare m k).K (GeneralPaperProxyParameters.prepare m k).S (operandWidth m k)

theorem source_scaling (model : RationalCostModel) (m k : ℕ) : GeneralPaperReferenceScaling.Scale (fun W => sourceProfile model W m k) := by
  unfold sourceProfile operandWidth GeneralPaperFinalPolytopeStorage.profile
    GeneralPaperFinalPolytopeStorage.callerProfile GeneralPaperFinalStaticStorage.profile GeneralPaperRayPredicateStorage.profile
    GeneralPaperFinalPolytopeStorage.metadataCap GeneralPaperFinalStaticLoopStorage.profile GeneralPaperFinalStaticStorage.callerProfile
    GeneralPaperRayPredicateStorage.metadataCap GeneralPaperRayQueryStorageEnvelope.profile GeneralPaperStaticEnumerationStorage.profile
    GeneralPaperStaticRowConstructionStorage.profile GeneralPaperStaticRowResidualStorage.profile GeneralPaperFinalPolytopeStorage.price
    GeneralPaperFinalStaticLoopStorage.frameProfile GeneralPaperFinalStaticStorage.metadataCap GeneralPaperRayPredicateStorage.price
    GeneralPaperRayQueryStorageEnvelope.constructionProfile GeneralPaperRayQueryStorageEnvelope.frameProfile GeneralPaperRayQueryStorageEnvelope.minimumProfile
    GeneralPaperScoreInitialStorage.profile GeneralPaperScoreLifetimeStorage.layerProfile GeneralPaperSparseResidualStorage.profile
    GeneralPaperStaticEnumerationStorage.callerProfile GeneralPaperStaticFamilyConstructionStorage.boxesProfile GeneralPaperStaticFamilyConstructionStorage.budgetsProfile
    GeneralPaperStaticFamilyConstructionStorage.ordersProfile GeneralPaperStaticRowConstructionStorage.budgetProfile GeneralPaperStaticRowConstructionStorage.orderProfile
    GeneralPaperStaticRowResidualStorage.metadataCap GeneralPaperStaticRowResidualStorage.rowProfile GeneralPaperAffineWitnessStorage.affineProfile
    GeneralPaperEncodedScoreMatrixStorage.matrixProfile GeneralPaperFinalPolytopeBits.profile GeneralPaperFinalStaticLoopStorage.metadataCap
    GeneralPaperFinalStaticStorage.scanPrice GeneralPaperHighMinimumStorage.profile GeneralPaperRayPredicateStorage.minimumPrice
    GeneralPaperRayQueryStorageEnvelope.costProfile GeneralPaperScoreConstructionStorage.stepProfile GeneralPaperScoreLifetimeStorage.callerProfile
    GeneralPaperSparseRayLoopStorage.frameProfile GeneralPaperSparseRayLoopStorage.zeroPrice GeneralPaperSparseResidualStorage.metadataCap
    GeneralPaperStaticEnumerationStorage.callerCap GeneralPaperStaticFamilyConstructionStorage.budgetCap GeneralPaperStaticFamilyConstructionStorage.callbackProfile
    GeneralPaperStaticFamilyConstructionStorage.familyCap GeneralPaperStaticRowConstructionStorage.budgetFrameProfile GeneralPaperStaticRowResidualStorage.generationCap
    GeneralPaperStaticVariableConstructionStorage.profile GeneralPaperStockListPayloadStorage.flattenProfile GeneralPaperStockListPayloadStorage.mapProfile
    GeneralPaperStockListPayloadStorage.ofFnProfile GeneralPaperEncodedScoreMatrixStorage.fieldProfile GeneralPaperFinRangeStorage.profile
    GeneralPaperFinalStaticLoopStorage.workCap GeneralPaperHighMinimumStorage.metadataCap GeneralPaperIndexedMinimumStorage.profile
    GeneralPaperNativeStaticScanStorage.count GeneralPaperNativeStaticScanStorage.enumerationPrice GeneralPaperNativeStaticScanStorage.indexProfile
    GeneralPaperNativeStaticScanStorage.rowPrice GeneralPaperPricedPayloadStreamStorage.flatProfile GeneralPaperRayMinimumBits.profile
    GeneralPaperScoreConstructionStorage.constructorProfile GeneralPaperScoreScanStorage.profile GeneralPaperScoreTableStorage.tableProfile
    GeneralPaperSparseRayLoopStorage.metadataCap GeneralPaperSparseRayStepStorage.profile GeneralPaperSparseResidualStorage.price
    GeneralPaperStaticFamilyConstructionStorage.budgetPrice GeneralPaperStaticFamilyConstructionStorage.callbackCap GeneralPaperStaticFamilyConstructionStorage.familyPrice
    GeneralPaperStaticRowConstructionStorage.controlCap GeneralPaperStaticRowConstructionStorage.referenceProfile GeneralPaperStaticScanPrice.profile
    GeneralPaperStaticVariableConstructionStorage.callerCap GeneralPaperStaticVariableConstructionStorage.innerProfile GeneralPaperStockListPayloadStorage.flattenFrameProfile
    GeneralPaperCommonLatticeMinimumBits.profile GeneralPaperEncodedScoreMatrixStorage.entryProfile GeneralPaperHighMinimumStorage.workCap
    GeneralPaperIndexedMinimumStorage.frameProfile GeneralPaperPayloadAppendStorage.profile GeneralPaperPricedPayloadStreamStorage.filterProfile
    GeneralPaperPricedPayloadStreamStorage.flatFrameProfile GeneralPaperScoreScanStorage.frameProfile GeneralPaperSparseRayLoopStorage.stepPrice
    GeneralPaperSparseRayStepStorage.cap GeneralPaperStaticRowResidualStorage.termProfile GeneralPaperStaticVariableConstructionStorage.innerCap
    GeneralPaperStaticVariableConstructionStorage.price GeneralPaperStaticVariableConstructionStorage.variableProfile GeneralPaperIndexedMinimumStorage.workCap
    GeneralPaperPayloadAppendStorage.frameProfile GeneralPaperPricedPayloadStreamStorage.filterFrameProfile GeneralPaperPricedPayloadStreamStorage.flatCap
    GeneralPaperPricedPayloadStreamStorage.listProfile GeneralPaperScoreLifetimeStorage.workCap GeneralPaperScoreScanStorage.workCap
    GeneralPaperScoreSelectionStorage.optionProfile GeneralPaperStaticVariableConstructionStorage.rowPrice GeneralPaperEncodedScalarStorage.natBits
    GeneralPaperPricedPayloadStreamStorage.filterCap GeneralPaperPricedPayloadStreamStorage.flatWork GeneralPaperPricedPayloadStreamStorage.optionProfile
    GeneralPaperScoreBitPrimitive.resourceWidth GeneralPaperScoreDPBits.profile GeneralPaperScoreSelectionStorage.selectionProfile
    GeneralPaperPricedPayloadStreamStorage.filterWork GeneralPaperScoreDPBits.initialProfile GeneralPaperScoreDPBits.stepProfile
    GeneralPaperSourceRawAffineStorageRates.operandWidth
  fun_prop

theorem source_model_mono (actual upper : RationalCostModel) (h : ∀ n,actual.rat n≤upper.rat n) (W m k : ℕ) :
    sourceProfile actual W m k≤sourceProfile upper W m k := by
  unfold sourceProfile operandWidth GeneralPaperFinalPolytopeStorage.profile
    GeneralPaperFinalPolytopeStorage.callerProfile GeneralPaperFinalStaticStorage.profile GeneralPaperRayPredicateStorage.profile
    GeneralPaperFinalPolytopeStorage.metadataCap GeneralPaperFinalStaticLoopStorage.profile GeneralPaperFinalStaticStorage.callerProfile
    GeneralPaperRayPredicateStorage.metadataCap GeneralPaperRayQueryStorageEnvelope.profile GeneralPaperStaticEnumerationStorage.profile
    GeneralPaperStaticRowConstructionStorage.profile GeneralPaperStaticRowResidualStorage.profile GeneralPaperFinalPolytopeStorage.price
    GeneralPaperFinalStaticLoopStorage.frameProfile GeneralPaperFinalStaticStorage.metadataCap GeneralPaperRayPredicateStorage.price
    GeneralPaperRayQueryStorageEnvelope.constructionProfile GeneralPaperRayQueryStorageEnvelope.frameProfile GeneralPaperRayQueryStorageEnvelope.minimumProfile
    GeneralPaperScoreInitialStorage.profile GeneralPaperScoreLifetimeStorage.layerProfile GeneralPaperSparseResidualStorage.profile
    GeneralPaperStaticEnumerationStorage.callerProfile GeneralPaperStaticFamilyConstructionStorage.boxesProfile GeneralPaperStaticFamilyConstructionStorage.budgetsProfile
    GeneralPaperStaticFamilyConstructionStorage.ordersProfile GeneralPaperStaticRowConstructionStorage.budgetProfile GeneralPaperStaticRowConstructionStorage.orderProfile
    GeneralPaperStaticRowResidualStorage.metadataCap GeneralPaperStaticRowResidualStorage.rowProfile GeneralPaperAffineWitnessStorage.affineProfile
    GeneralPaperEncodedScoreMatrixStorage.matrixProfile GeneralPaperFinalPolytopeBits.profile GeneralPaperFinalStaticLoopStorage.metadataCap
    GeneralPaperFinalStaticStorage.scanPrice GeneralPaperHighMinimumStorage.profile GeneralPaperRayPredicateStorage.minimumPrice
    GeneralPaperRayQueryStorageEnvelope.costProfile GeneralPaperScoreConstructionStorage.stepProfile GeneralPaperScoreLifetimeStorage.callerProfile
    GeneralPaperSparseRayLoopStorage.frameProfile GeneralPaperSparseRayLoopStorage.zeroPrice GeneralPaperSparseResidualStorage.metadataCap
    GeneralPaperStaticEnumerationStorage.callerCap GeneralPaperStaticFamilyConstructionStorage.budgetCap GeneralPaperStaticFamilyConstructionStorage.callbackProfile
    GeneralPaperStaticFamilyConstructionStorage.familyCap GeneralPaperStaticRowConstructionStorage.budgetFrameProfile GeneralPaperStaticRowResidualStorage.generationCap
    GeneralPaperStaticVariableConstructionStorage.profile GeneralPaperStockListPayloadStorage.flattenProfile GeneralPaperStockListPayloadStorage.mapProfile
    GeneralPaperStockListPayloadStorage.ofFnProfile GeneralPaperEncodedScoreMatrixStorage.fieldProfile GeneralPaperFinRangeStorage.profile
    GeneralPaperFinalStaticLoopStorage.workCap GeneralPaperHighMinimumStorage.metadataCap GeneralPaperIndexedMinimumStorage.profile
    GeneralPaperNativeStaticScanStorage.count GeneralPaperNativeStaticScanStorage.enumerationPrice GeneralPaperNativeStaticScanStorage.indexProfile
    GeneralPaperNativeStaticScanStorage.rowPrice GeneralPaperPricedPayloadStreamStorage.flatProfile GeneralPaperRayMinimumBits.profile
    GeneralPaperScoreConstructionStorage.constructorProfile GeneralPaperScoreScanStorage.profile GeneralPaperScoreTableStorage.tableProfile
    GeneralPaperSparseRayLoopStorage.metadataCap GeneralPaperSparseRayStepStorage.profile GeneralPaperSparseResidualStorage.price
    GeneralPaperStaticFamilyConstructionStorage.budgetPrice GeneralPaperStaticFamilyConstructionStorage.callbackCap GeneralPaperStaticFamilyConstructionStorage.familyPrice
    GeneralPaperStaticRowConstructionStorage.controlCap GeneralPaperStaticRowConstructionStorage.referenceProfile GeneralPaperStaticScanPrice.profile
    GeneralPaperStaticVariableConstructionStorage.callerCap GeneralPaperStaticVariableConstructionStorage.innerProfile GeneralPaperStockListPayloadStorage.flattenFrameProfile
    GeneralPaperCommonLatticeMinimumBits.profile GeneralPaperEncodedScoreMatrixStorage.entryProfile GeneralPaperHighMinimumStorage.workCap
    GeneralPaperIndexedMinimumStorage.frameProfile GeneralPaperPayloadAppendStorage.profile GeneralPaperPricedPayloadStreamStorage.filterProfile
    GeneralPaperPricedPayloadStreamStorage.flatFrameProfile GeneralPaperScoreScanStorage.frameProfile GeneralPaperSparseRayLoopStorage.stepPrice
    GeneralPaperSparseRayStepStorage.cap GeneralPaperStaticRowResidualStorage.termProfile GeneralPaperStaticVariableConstructionStorage.innerCap
    GeneralPaperStaticVariableConstructionStorage.price GeneralPaperStaticVariableConstructionStorage.variableProfile GeneralPaperIndexedMinimumStorage.workCap
    GeneralPaperPayloadAppendStorage.frameProfile GeneralPaperPricedPayloadStreamStorage.filterFrameProfile GeneralPaperPricedPayloadStreamStorage.flatCap
    GeneralPaperPricedPayloadStreamStorage.listProfile GeneralPaperScoreLifetimeStorage.workCap GeneralPaperScoreScanStorage.workCap
    GeneralPaperScoreSelectionStorage.optionProfile GeneralPaperStaticVariableConstructionStorage.rowPrice GeneralPaperEncodedScalarStorage.natBits
    GeneralPaperPricedPayloadStreamStorage.filterCap GeneralPaperPricedPayloadStreamStorage.flatWork GeneralPaperPricedPayloadStreamStorage.optionProfile
    GeneralPaperScoreBitPrimitive.resourceWidth GeneralPaperScoreDPBits.profile GeneralPaperScoreSelectionStorage.selectionProfile
    GeneralPaperPricedPayloadStreamStorage.filterWork GeneralPaperScoreDPBits.initialProfile GeneralPaperScoreDPBits.stepProfile
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
  refine ⟨_,_,_,by
    unfold sourceProfile operandWidth GeneralPaperFinalPolytopeStorage.profile
      GeneralPaperFinalPolytopeStorage.callerProfile GeneralPaperFinalStaticStorage.profile GeneralPaperRayPredicateStorage.profile
      GeneralPaperFinalPolytopeStorage.metadataCap GeneralPaperFinalStaticLoopStorage.profile GeneralPaperFinalStaticStorage.callerProfile
      GeneralPaperRayPredicateStorage.metadataCap GeneralPaperRayQueryStorageEnvelope.profile GeneralPaperStaticEnumerationStorage.profile
      GeneralPaperStaticRowConstructionStorage.profile GeneralPaperStaticRowResidualStorage.profile GeneralPaperFinalPolytopeStorage.price
      GeneralPaperFinalStaticLoopStorage.frameProfile GeneralPaperFinalStaticStorage.metadataCap GeneralPaperRayPredicateStorage.price
      GeneralPaperRayQueryStorageEnvelope.constructionProfile GeneralPaperRayQueryStorageEnvelope.frameProfile GeneralPaperRayQueryStorageEnvelope.minimumProfile
      GeneralPaperScoreInitialStorage.profile GeneralPaperScoreLifetimeStorage.layerProfile GeneralPaperSparseResidualStorage.profile
      GeneralPaperStaticEnumerationStorage.callerProfile GeneralPaperStaticFamilyConstructionStorage.boxesProfile GeneralPaperStaticFamilyConstructionStorage.budgetsProfile
      GeneralPaperStaticFamilyConstructionStorage.ordersProfile GeneralPaperStaticRowConstructionStorage.budgetProfile GeneralPaperStaticRowConstructionStorage.orderProfile
      GeneralPaperStaticRowResidualStorage.metadataCap GeneralPaperStaticRowResidualStorage.rowProfile GeneralPaperAffineWitnessStorage.affineProfile
      GeneralPaperEncodedScoreMatrixStorage.matrixProfile GeneralPaperFinalPolytopeBits.profile GeneralPaperFinalStaticLoopStorage.metadataCap
      GeneralPaperFinalStaticStorage.scanPrice GeneralPaperHighMinimumStorage.profile GeneralPaperRayPredicateStorage.minimumPrice
      GeneralPaperRayQueryStorageEnvelope.costProfile GeneralPaperScoreConstructionStorage.stepProfile GeneralPaperScoreLifetimeStorage.callerProfile
      GeneralPaperSparseRayLoopStorage.frameProfile GeneralPaperSparseRayLoopStorage.zeroPrice GeneralPaperSparseResidualStorage.metadataCap
      GeneralPaperStaticEnumerationStorage.callerCap GeneralPaperStaticFamilyConstructionStorage.budgetCap GeneralPaperStaticFamilyConstructionStorage.callbackProfile
      GeneralPaperStaticFamilyConstructionStorage.familyCap GeneralPaperStaticRowConstructionStorage.budgetFrameProfile GeneralPaperStaticRowResidualStorage.generationCap
      GeneralPaperStaticVariableConstructionStorage.profile GeneralPaperStockListPayloadStorage.flattenProfile GeneralPaperStockListPayloadStorage.mapProfile
      GeneralPaperStockListPayloadStorage.ofFnProfile GeneralPaperEncodedScoreMatrixStorage.fieldProfile GeneralPaperFinRangeStorage.profile
      GeneralPaperFinalStaticLoopStorage.workCap GeneralPaperHighMinimumStorage.metadataCap GeneralPaperIndexedMinimumStorage.profile
      GeneralPaperNativeStaticScanStorage.count GeneralPaperNativeStaticScanStorage.enumerationPrice GeneralPaperNativeStaticScanStorage.indexProfile
      GeneralPaperNativeStaticScanStorage.rowPrice GeneralPaperPricedPayloadStreamStorage.flatProfile GeneralPaperRayMinimumBits.profile
      GeneralPaperScoreConstructionStorage.constructorProfile GeneralPaperScoreScanStorage.profile GeneralPaperScoreTableStorage.tableProfile
      GeneralPaperSparseRayLoopStorage.metadataCap GeneralPaperSparseRayStepStorage.profile GeneralPaperSparseResidualStorage.price
      GeneralPaperStaticFamilyConstructionStorage.budgetPrice GeneralPaperStaticFamilyConstructionStorage.callbackCap GeneralPaperStaticFamilyConstructionStorage.familyPrice
      GeneralPaperStaticRowConstructionStorage.controlCap GeneralPaperStaticRowConstructionStorage.referenceProfile GeneralPaperStaticScanPrice.profile
      GeneralPaperStaticVariableConstructionStorage.callerCap GeneralPaperStaticVariableConstructionStorage.innerProfile GeneralPaperStockListPayloadStorage.flattenFrameProfile
      GeneralPaperCommonLatticeMinimumBits.profile GeneralPaperEncodedScoreMatrixStorage.entryProfile GeneralPaperHighMinimumStorage.workCap
      GeneralPaperIndexedMinimumStorage.frameProfile GeneralPaperPayloadAppendStorage.profile GeneralPaperPricedPayloadStreamStorage.filterProfile
      GeneralPaperPricedPayloadStreamStorage.flatFrameProfile GeneralPaperScoreScanStorage.frameProfile GeneralPaperSparseRayLoopStorage.stepPrice
      GeneralPaperSparseRayStepStorage.cap GeneralPaperStaticRowResidualStorage.termProfile GeneralPaperStaticVariableConstructionStorage.innerCap
      GeneralPaperStaticVariableConstructionStorage.price GeneralPaperStaticVariableConstructionStorage.variableProfile GeneralPaperIndexedMinimumStorage.workCap
      GeneralPaperPayloadAppendStorage.frameProfile GeneralPaperPricedPayloadStreamStorage.filterFrameProfile GeneralPaperPricedPayloadStreamStorage.flatCap
      GeneralPaperPricedPayloadStreamStorage.listProfile GeneralPaperScoreLifetimeStorage.workCap GeneralPaperScoreScanStorage.workCap
      GeneralPaperScoreSelectionStorage.optionProfile GeneralPaperStaticVariableConstructionStorage.rowPrice GeneralPaperEncodedScalarStorage.natBits
      GeneralPaperPricedPayloadStreamStorage.filterCap GeneralPaperPricedPayloadStreamStorage.flatWork GeneralPaperPricedPayloadStreamStorage.optionProfile
      GeneralPaperScoreBitPrimitive.resourceWidth GeneralPaperScoreDPBits.profile GeneralPaperScoreSelectionStorage.selectionProfile
      GeneralPaperPricedPayloadStreamStorage.filterWork GeneralPaperScoreDPBits.initialProfile GeneralPaperScoreDPBits.stepProfile
      GeneralPaperSourceRawAffineStorageRates.operandWidth
    dsimp only [GeneralPaperFastRationalMajorant.model]
    source_space⟩

theorem degrees (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    ((certificate C d W hW).fields,(certificate C d W hW).symbols,(certificate C d W hW).accuracy)=(3,0,4) := rfl

def reservation (model : RationalCostModel) (W m k : ℕ) : ℕ := GeneralPaperSourceRawAffineStorageRates.reservation model W m k+sourceProfile model W m k
def reservationCertificate (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    Certificate (fun x => reservation (GeneralPaperFastRationalMajorant.model C d) (W x) x.m x.k) := by
  have hOld := (GeneralPaperSourceRawAffineStorageRates.reservationCertificate C d W hW).bound
  have hNew := (certificate C d W hW).bound
  refine ⟨_,_,_,by unfold reservation; source_space⟩

theorem reservation_degrees (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    ((reservationCertificate C d W hW).fields,(reservationCertificate C d W hW).symbols,(reservationCertificate C d W hW).accuracy)=(3,0,4) := rfl

theorem reservation_scaling (model : RationalCostModel) (m k : ℕ) : GeneralPaperReferenceScaling.Scale (fun W => reservation model W m k) := by
  have hOld := GeneralPaperSourceRawAffineStorageRates.reservation_scaling model m k
  have hNew := source_scaling model m k
  unfold reservation
  fun_prop

theorem reservation_mono (actual upper : RationalCostModel) (h : ∀ n,actual.rat n≤upper.rat n) (W m k : ℕ) :
    reservation actual W m k≤reservation upper W m k :=
  Nat.add_le_add (GeneralPaperSourceRawAffineStorageRates.reservation_mono actual upper h W m k) (source_model_mono actual upper h W m k)

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

end Blotto.GeneralPaperSourceFinalCheckStorageRates
