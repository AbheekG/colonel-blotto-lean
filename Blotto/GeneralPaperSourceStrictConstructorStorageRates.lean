import Blotto.GeneralPaperRetainedStrictParentStorage

/-! Literal strict-preparation parent, full matrix constructors and
recursive strict DP layer storage have sharp degrees (1,0,1), (2,0,2)
and (3,0,2). Their SUM with preceding reserves preserves (3,0,4). -/
namespace Blotto.GeneralPaperSourceStrictConstructorStorageRates
open GeneralPaperSourceWordGrowth GeneralPaperSourceSoftBounds GeneralPaperSourceRateAlgebra
open GeneralPaperConstructedWordGrowth GeneralPaperCompilerReferenceGrowth
set_option autoImplicit false
set_option maxHeartbeats 7000000
set_option maxRecDepth 16384

def operandWidth (m k : ℕ) : ℕ := 1+4*binaryWordWidth (GeneralPaperProxyParameters.prepare m k).qbar
def parentProfile (model : RationalCostModel) (W m k Qv : ℕ) : ℕ := GeneralPaperRetainedStrictParentStorage.profile model W m
  (GeneralPaperProxyParameters.prepare m k).K (GeneralPaperProxyParameters.prepare m k).S (GeneralPaperScoreScaleParameters.prepare m k).depth
  (operandWidth m k) (GeneralPaperSourceStrictPreparationBits.profile model W m k Qv)
def sourceProfile (model : RationalCostModel) (W m k Qv : ℕ) : ℕ := parentProfile model W m k Qv+
  GeneralPaperSourceMatrixStorage.sourceProfile model W m k Qv+GeneralPaperSourceScoreStorage.profile model W m k

theorem parent_scaling (model : RationalCostModel) (m k Qv : ℕ) : GeneralPaperReferenceScaling.Scale (fun W => parentProfile model W m k Qv) := by
  unfold parentProfile operandWidth GeneralPaperRetainedStrictParentStorage.profile
    GeneralPaperSourceStrictPreparationBits.profile GeneralPaperEncodedScalarStorage.natBits GeneralPaperRetainedStrictParentStorage.metadataCap
    GeneralPaperRetainedTransferPrice.bitProfile GeneralPaperScoreDPBits.profile GeneralPaperScoreMatrixBits.matrixProfile
    GeneralPaperSummaryArrayExecution.arrayWord GeneralPaperThresholdScanBits.profile
    GeneralPaperScoreDPBits.initialProfile GeneralPaperScoreDPBits.stepProfile GeneralPaperScoreMatrixBits.fieldProfile
    GeneralPaperThresholdScanBits.comparisonWidth GeneralPaperScoreBitPrimitive.resourceWidth GeneralPaperScoreMatrixBits.entryProfile
    GeneralPaperScoreMatrixBits.scoreProfile GeneralPaperScoreArgumentBits.argumentProfile GeneralPaperScoreArgumentBits.height
    GeneralPaperBoundedQuotient.bitProfile GeneralPaperBoundedQuotient.heightBudget
  fun_prop

theorem parent_model_mono (actual upper : RationalCostModel) (h : ∀ n,actual.rat n≤upper.rat n) (W m k Qv : ℕ) :
    parentProfile actual W m k Qv≤parentProfile upper W m k Qv := by
  unfold parentProfile operandWidth GeneralPaperRetainedStrictParentStorage.profile
    GeneralPaperSourceStrictPreparationBits.profile GeneralPaperEncodedScalarStorage.natBits GeneralPaperRetainedStrictParentStorage.metadataCap
    GeneralPaperRetainedTransferPrice.bitProfile GeneralPaperScoreDPBits.profile GeneralPaperScoreMatrixBits.matrixProfile
    GeneralPaperSummaryArrayExecution.arrayWord GeneralPaperThresholdScanBits.profile
    GeneralPaperScoreDPBits.initialProfile GeneralPaperScoreDPBits.stepProfile GeneralPaperScoreMatrixBits.fieldProfile
    GeneralPaperThresholdScanBits.comparisonWidth GeneralPaperScoreBitPrimitive.resourceWidth GeneralPaperScoreMatrixBits.entryProfile
    GeneralPaperScoreMatrixBits.scoreProfile GeneralPaperScoreArgumentBits.argumentProfile GeneralPaperScoreArgumentBits.height
    GeneralPaperBoundedQuotient.bitProfile GeneralPaperBoundedQuotient.heightBudget
  gcongr <;> exact h _

def parentCertificate (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    Certificate (fun x => parentProfile (GeneralPaperFastRationalMajorant.model C d) (W x) x.m x.k x.Qv) := by
  have hr : Rated W 0 0 0 := poly (poly_tight W hW)
  have hs := of_tight hW
  have hA := GeneralPaperSourceSharpOperandRates.anchor_height
  have hCap := GeneralPaperSourceSharpOperandRates.cap_word
  refine ⟨_,_,_,by
    unfold parentProfile operandWidth GeneralPaperRetainedStrictParentStorage.profile
      GeneralPaperSourceStrictPreparationBits.profile GeneralPaperEncodedScalarStorage.natBits GeneralPaperRetainedStrictParentStorage.metadataCap
      GeneralPaperRetainedTransferPrice.bitProfile GeneralPaperScoreDPBits.profile GeneralPaperScoreMatrixBits.matrixProfile
      GeneralPaperSummaryArrayExecution.arrayWord GeneralPaperThresholdScanBits.profile
      GeneralPaperScoreDPBits.initialProfile GeneralPaperScoreDPBits.stepProfile GeneralPaperScoreMatrixBits.fieldProfile
      GeneralPaperThresholdScanBits.comparisonWidth GeneralPaperScoreBitPrimitive.resourceWidth GeneralPaperScoreMatrixBits.entryProfile
      GeneralPaperScoreMatrixBits.scoreProfile GeneralPaperScoreArgumentBits.argumentProfile GeneralPaperScoreArgumentBits.height
      GeneralPaperBoundedQuotient.bitProfile GeneralPaperBoundedQuotient.heightBudget
    dsimp only [GeneralPaperFastRationalMajorant.model]
    source_space⟩

theorem parent_degrees (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    ((parentCertificate C d W hW).fields,(parentCertificate C d W hW).symbols,(parentCertificate C d W hW).accuracy)=(1,0,1) := rfl

def matrixCertificate (C d : ℕ) (W : Input → ℕ) (hW : Tight W) : Certificate (fun x =>
    GeneralPaperSourceMatrixStorage.sourceProfile (GeneralPaperFastRationalMajorant.model C d) (W x) x.m x.k x.Qv) := by
  have hr : Rated W 0 0 0 := poly (poly_tight W hW)
  have hs := of_tight hW
  have hA := GeneralPaperSourceSharpOperandRates.anchor_height
  have hCap := GeneralPaperSourceSharpOperandRates.cap_word
  refine ⟨_,_,_,by
    unfold GeneralPaperSourceMatrixStorage.sourceProfile GeneralPaperSourceMatrixStorage.profile
      GeneralPaperSourceMatrixStorage.metadataCap GeneralPaperSourceMatrixStorage.physicalPrice
      GeneralPaperScoreMatrixEntryStorage.profile GeneralPaperScoreMatrixConstructionStorage.profile
      GeneralPaperScoreConstructionStorage.constructorProfile GeneralPaperEncodedScoreMatrixStorage.matrixProfile
      GeneralPaperEncodedScoreMatrixStorage.fieldProfile GeneralPaperEncodedScoreMatrixStorage.entryProfile
      GeneralPaperScoreEntryStorage.profile GeneralPaperScoreEntryStorage.metadataCap
      GeneralPaperScoreArgumentStorage.profile GeneralPaperBitQuotientStorage.profile
      GeneralPaperBitQuotientStorage.counterFrameProfile GeneralPaperBitQuotientStorage.metadataCap
      GeneralPaperQuotientConstructionStorage.frameCap GeneralPaperQuotientConstructionStorage.localCap
      GeneralPaperScoreMatrixBits.matrixProfile GeneralPaperScoreMatrixBits.fieldProfile
      GeneralPaperScoreMatrixBits.entryProfile GeneralPaperScoreMatrixBits.scoreProfile
      GeneralPaperScoreArgumentBits.argumentProfile GeneralPaperScoreArgumentBits.height
      GeneralPaperBoundedQuotient.bitProfile GeneralPaperBoundedQuotient.heightBudget
      GeneralPaperEncodedScalarStorage.natBits GeneralPaperSummaryArrayExecution.arrayWord
    unfold GeneralPaperEncodedScoreMatrixStorage.entryProfile GeneralPaperEncodedScalarStorage.natBits
    dsimp only [GeneralPaperFastRationalMajorant.model]
    source_space⟩

theorem matrixCertificate_degrees (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    ((matrixCertificate C d W hW).fields,(matrixCertificate C d W hW).symbols,(matrixCertificate C d W hW).accuracy)=(2,0,2) := rfl

def dpCertificate (C d : ℕ) (W : Input → ℕ) (hW : Tight W) : Certificate (fun x =>
    GeneralPaperSourceScoreStorage.profile (GeneralPaperFastRationalMajorant.model C d) (W x) x.m x.k) := by
  have hR : Rated W 0 0 0 := poly (poly_tight W hW)
  have hSmall := of_tight hW
  have hA := GeneralPaperSourceSharpOperandRates.anchor_height
  have hCap := GeneralPaperSourceSharpOperandRates.cap_word
  refine ⟨_,_,_,by
    unfold GeneralPaperSourceScoreStorage.profile GeneralPaperScoreLifetimeStorage.layerProfile
      GeneralPaperScoreLifetimeStorage.callerProfile GeneralPaperScoreLifetimeStorage.workCap
      GeneralPaperScoreConstructionStorage.stepProfile GeneralPaperScoreConstructionStorage.constructorProfile
      GeneralPaperScoreScanStorage.profile GeneralPaperScoreScanStorage.frameProfile GeneralPaperScoreScanStorage.workCap
      GeneralPaperScoreDPBits.profile GeneralPaperScoreDPBits.initialProfile GeneralPaperScoreDPBits.stepProfile
      GeneralPaperScoreTableStorage.tableProfile GeneralPaperScoreSelectionStorage.optionProfile
      GeneralPaperScoreSelectionStorage.selectionProfile GeneralPaperEncodedScalarStorage.natBits
      GeneralPaperScoreBitPrimitive.resourceWidth
    dsimp only [GeneralPaperFastRationalMajorant.model]
    source_space⟩

theorem dpCertificate_degrees (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    ((dpCertificate C d W hW).fields,(dpCertificate C d W hW).symbols,(dpCertificate C d W hW).accuracy)=(3,0,2) := rfl

theorem source_scaling (model : RationalCostModel) (m k Qv : ℕ) : GeneralPaperReferenceScaling.Scale (fun W => sourceProfile model W m k Qv) := by
  have hp := parent_scaling model m k Qv
  have hm := GeneralPaperScoreEntryStorageRates.scaling model m k Qv
  have hd := GeneralPaperScoreStorageRates.scaling model m k
  unfold sourceProfile
  fun_prop

theorem source_model_mono (actual upper : RationalCostModel) (h : ∀ n,actual.rat n≤upper.rat n) (W m k Qv : ℕ) :
    sourceProfile actual W m k Qv≤sourceProfile upper W m k Qv :=
  Nat.add_le_add (Nat.add_le_add (parent_model_mono actual upper h W m k Qv)
    (GeneralPaperScoreEntryStorageRates.profile_mono actual upper h W m k Qv))
    (GeneralPaperScoreStorageRates.profile_mono actual upper h W m k)

def certificate (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    Certificate (fun x => sourceProfile (GeneralPaperFastRationalMajorant.model C d) (W x) x.m x.k x.Qv) := by
  refine ⟨3,0,2,?_⟩
  exact GeneralPaperSourceRateAlgebra.add _ _ 2 0 2 3 0 2
    (GeneralPaperSourceRateAlgebra.add _ _ 1 0 1 2 0 2 (parentCertificate C d W hW).bound (matrixCertificate C d W hW).bound)
    (dpCertificate C d W hW).bound

theorem degrees (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    ((certificate C d W hW).fields,(certificate C d W hW).symbols,(certificate C d W hW).accuracy)=(3,0,2) := rfl

def reservation (model : RationalCostModel) (W m k Qv : ℕ) : ℕ := GeneralPaperSourceEnclosingOwnerRates.reservation model W m k+sourceProfile model W m k Qv

def reservationCertificate (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    Certificate (fun x => reservation (GeneralPaperFastRationalMajorant.model C d) (W x) x.m x.k x.Qv) := by
  refine ⟨3,0,4,?_⟩
  exact GeneralPaperSourceRateAlgebra.add _ _ 3 0 4 3 0 2
    (GeneralPaperSourceEnclosingOwnerRates.reservationCertificate C d W hW).bound (certificate C d W hW).bound

theorem reservation_degrees (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    ((reservationCertificate C d W hW).fields,(reservationCertificate C d W hW).symbols,(reservationCertificate C d W hW).accuracy)=(3,0,4) := rfl

theorem reservation_scaling (model : RationalCostModel) (m k Qv : ℕ) : GeneralPaperReferenceScaling.Scale (fun W => reservation model W m k Qv) := by
  have hOld := GeneralPaperSourceEnclosingOwnerRates.reservation_scaling model m k
  have hNew := source_scaling model m k Qv
  unfold reservation
  fun_prop

theorem reservation_mono (actual upper : RationalCostModel) (h : ∀ n,actual.rat n≤upper.rat n) (W m k Qv : ℕ) :
    reservation actual W m k Qv≤reservation upper W m k Qv :=
  Nat.add_le_add (GeneralPaperSourceEnclosingOwnerRates.reservation_mono actual upper h W m k) (source_model_mono actual upper h W m k Qv)

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

end Blotto.GeneralPaperSourceStrictConstructorStorageRates
