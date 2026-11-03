import Blotto.GeneralPaperSourceStrictChildWindows

/-! Initial empty-table/matrix/caller, full strict-threshold scan and
stored-maximum/guard child windows have sharp (2,0,2), (3,0,2), (3,0,2).
Their SUM with preceding native strict/source reserves preserves (3,0,4). -/
namespace Blotto.GeneralPaperSourceStrictChildStorageRates
open GeneralPaperSourceWordGrowth GeneralPaperSourceSoftBounds GeneralPaperSourceRateAlgebra
open GeneralPaperConstructedWordGrowth GeneralPaperCompilerReferenceGrowth
set_option autoImplicit false
set_option maxHeartbeats 7000000
set_option maxRecDepth 16384

def sourceProfile (model : RationalCostModel) (W m k Qv : ℕ) : ℕ :=
  GeneralPaperScoreResidencyRates.initialProfile model W m k+
    GeneralPaperSourceScoreResidents.thresholdProfile model W m k+GeneralPaperSourceGuardStorage.sourceProfile model W m k Qv

def initialCertificate (C d : ℕ) (W : Input → ℕ) (hW : Tight W) : Certificate (fun x =>
    GeneralPaperScoreResidencyRates.initialProfile (GeneralPaperFastRationalMajorant.model C d) (W x) x.m x.k) := by
  have hr : Rated W 0 0 0 := poly (poly_tight W hW)
  have hs := of_tight hW
  have hA := GeneralPaperSourceSharpOperandRates.anchor_height
  have hCap := GeneralPaperSourceSharpOperandRates.cap_word
  refine ⟨_,_,_,by
    unfold GeneralPaperScoreResidencyRates.initialProfile GeneralPaperSourceScoreResidents.residentProfile GeneralPaperScoreResidentPhases.residentProfile
      GeneralPaperEncodedScoreMatrixStorage.matrixProfile GeneralPaperEncodedScoreMatrixStorage.fieldProfile
      GeneralPaperEncodedScoreMatrixStorage.entryProfile GeneralPaperScoreInitialStorage.profile
      GeneralPaperScoreTableStorage.tableProfile GeneralPaperScoreSelectionStorage.optionProfile
      GeneralPaperScoreSelectionStorage.selectionProfile GeneralPaperScoreConstructionStorage.constructorProfile
      GeneralPaperScoreLifetimeStorage.callerProfile GeneralPaperScoreLifetimeStorage.workCap
      GeneralPaperScoreDPBits.profile GeneralPaperScoreDPBits.initialProfile GeneralPaperScoreDPBits.stepProfile
      GeneralPaperScoreBitPrimitive.resourceWidth GeneralPaperEncodedScalarStorage.natBits
    dsimp only [GeneralPaperFastRationalMajorant.model]
    source_space⟩

theorem initialCertificate_degrees (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    ((initialCertificate C d W hW).fields,(initialCertificate C d W hW).symbols,(initialCertificate C d W hW).accuracy)=(2,0,2) := rfl

def thresholdCertificate (C d : ℕ) (W : Input → ℕ) (hW : Tight W) : Certificate (fun x =>
    GeneralPaperSourceScoreResidents.thresholdProfile (GeneralPaperFastRationalMajorant.model C d) (W x) x.m x.k) := by
  have hr : Rated W 0 0 0 := poly (poly_tight W hW)
  have hs := of_tight hW
  have hA := GeneralPaperSourceSharpOperandRates.anchor_height
  have hCap := GeneralPaperSourceSharpOperandRates.cap_word
  refine ⟨_,_,_,by
    unfold GeneralPaperSourceScoreResidents.thresholdProfile GeneralPaperScoreResidentPhases.thresholdProfile
      GeneralPaperScoreResidentPhases.residentProfile GeneralPaperEncodedScoreMatrixStorage.matrixProfile
      GeneralPaperEncodedScoreMatrixStorage.fieldProfile GeneralPaperEncodedScoreMatrixStorage.entryProfile
      GeneralPaperThresholdScanStorage.profile GeneralPaperThresholdScanStorage.frameProfile GeneralPaperThresholdScanStorage.cap
      GeneralPaperScoreTableStorage.tableProfile GeneralPaperScoreSelectionStorage.optionProfile
      GeneralPaperScoreSelectionStorage.selectionProfile GeneralPaperThresholdScanBits.comparisonWidth
      GeneralPaperScoreBitPrimitive.resourceWidth GeneralPaperEncodedScalarStorage.natBits
    dsimp only [GeneralPaperFastRationalMajorant.model]
    source_space⟩

theorem thresholdCertificate_degrees (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    ((thresholdCertificate C d W hW).fields,(thresholdCertificate C d W hW).symbols,(thresholdCertificate C d W hW).accuracy)=(3,0,2) := rfl

def guardCertificate (C d : ℕ) (W : Input → ℕ) (hW : Tight W) : Certificate (fun x =>
    GeneralPaperSourceGuardStorage.sourceProfile (GeneralPaperFastRationalMajorant.model C d) (W x) x.m x.k x.Qv) := by
  have hr : Rated W 0 0 0 := poly (poly_tight W hW)
  have hs := of_tight hW
  have hA := GeneralPaperSourceSharpOperandRates.anchor_height
  have hCap := GeneralPaperSourceSharpOperandRates.cap_word
  refine ⟨_,_,_,by
    unfold GeneralPaperSourceGuardStorage.sourceProfile GeneralPaperSourceGuardStorage.profile
      GeneralPaperSourceGuardStorage.metadataCap GeneralPaperSourceGuardStorage.price
      GeneralPaperScoreResidentPhases.residentProfile GeneralPaperEncodedScoreMatrixStorage.matrixProfile
      GeneralPaperEncodedScoreMatrixStorage.fieldProfile GeneralPaperEncodedScoreMatrixStorage.entryProfile
      GeneralPaperScoreTableStorage.tableProfile GeneralPaperScoreSelectionStorage.optionProfile
      GeneralPaperScoreSelectionStorage.selectionProfile GeneralPaperEncodedRationalRows.rowProfile
      GeneralPaperStoredMaximumStorage.profile GeneralPaperStoredMaximumStorage.metadataCap
      GeneralPaperStoredMaximumStorage.loadPrice GeneralPaperStoredMaximumStorage.maximumPrice
      GeneralPaperNaturalSumStorage.profile GeneralPaperNaturalSumStorage.frameProfile
      GeneralPaperNaturalSumStorage.metadataCap GeneralPaperNaturalSumStorage.workCap
      GeneralPaperScoreConstructionStorage.constructorProfile GeneralPaperRetainedTransferPrice.bitProfile
      GeneralPaperScoreMatrixBits.matrixProfile GeneralPaperScoreMatrixBits.fieldProfile
      GeneralPaperScoreMatrixBits.entryProfile GeneralPaperScoreMatrixBits.scoreProfile
      GeneralPaperScoreArgumentBits.argumentProfile GeneralPaperScoreArgumentBits.height
      GeneralPaperBoundedQuotient.bitProfile GeneralPaperBoundedQuotient.heightBudget
      GeneralPaperScoreDPBits.profile GeneralPaperScoreDPBits.stepProfile GeneralPaperScoreDPBits.initialProfile
      GeneralPaperThresholdScanBits.profile GeneralPaperThresholdScanBits.comparisonWidth
      GeneralPaperScoreBitPrimitive.resourceWidth GeneralPaperEncodedScalarStorage.natBits
      GeneralPaperSummaryArrayExecution.arrayWord
    dsimp only [GeneralPaperFastRationalMajorant.model]
    source_space⟩

theorem guard_degrees (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    ((guardCertificate C d W hW).fields,(guardCertificate C d W hW).symbols,(guardCertificate C d W hW).accuracy)=(3,0,2) := rfl

theorem initial_scaling (model : RationalCostModel) (m k : ℕ) : GeneralPaperReferenceScaling.Scale (fun W => GeneralPaperScoreResidencyRates.initialProfile model W m k) := by
  unfold GeneralPaperScoreResidencyRates.initialProfile GeneralPaperSourceScoreResidents.residentProfile GeneralPaperScoreResidentPhases.residentProfile
    GeneralPaperEncodedScoreMatrixStorage.matrixProfile GeneralPaperEncodedScoreMatrixStorage.fieldProfile
    GeneralPaperEncodedScoreMatrixStorage.entryProfile GeneralPaperScoreInitialStorage.profile
    GeneralPaperScoreTableStorage.tableProfile GeneralPaperScoreSelectionStorage.optionProfile
    GeneralPaperScoreSelectionStorage.selectionProfile GeneralPaperScoreConstructionStorage.constructorProfile
    GeneralPaperScoreLifetimeStorage.callerProfile GeneralPaperScoreLifetimeStorage.workCap
    GeneralPaperScoreDPBits.profile GeneralPaperScoreDPBits.initialProfile GeneralPaperScoreDPBits.stepProfile
    GeneralPaperScoreBitPrimitive.resourceWidth GeneralPaperEncodedScalarStorage.natBits
  fun_prop

theorem initial_model_mono (actual upper : RationalCostModel) (h : ∀ n,actual.rat n≤upper.rat n) (W m k : ℕ) :
    GeneralPaperScoreResidencyRates.initialProfile actual W m k≤GeneralPaperScoreResidencyRates.initialProfile upper W m k := by
  unfold GeneralPaperScoreResidencyRates.initialProfile GeneralPaperSourceScoreResidents.residentProfile GeneralPaperScoreResidentPhases.residentProfile
    GeneralPaperEncodedScoreMatrixStorage.matrixProfile GeneralPaperEncodedScoreMatrixStorage.fieldProfile
    GeneralPaperEncodedScoreMatrixStorage.entryProfile GeneralPaperScoreInitialStorage.profile
    GeneralPaperScoreTableStorage.tableProfile GeneralPaperScoreSelectionStorage.optionProfile
    GeneralPaperScoreSelectionStorage.selectionProfile GeneralPaperScoreConstructionStorage.constructorProfile
    GeneralPaperScoreLifetimeStorage.callerProfile GeneralPaperScoreLifetimeStorage.workCap
    GeneralPaperScoreDPBits.profile GeneralPaperScoreDPBits.initialProfile GeneralPaperScoreDPBits.stepProfile
    GeneralPaperScoreBitPrimitive.resourceWidth GeneralPaperEncodedScalarStorage.natBits
  dsimp only
  gcongr
  exact h _

theorem source_scaling (model : RationalCostModel) (m k Qv : ℕ) : GeneralPaperReferenceScaling.Scale (fun W => sourceProfile model W m k Qv) := by
  have hi := initial_scaling model m k
  have ht := GeneralPaperScoreResidencyRates.threshold_scaling model m k
  have hg := GeneralPaperGuardMinimumStorageRates.guard_scaling model m k Qv
  unfold sourceProfile
  fun_prop

theorem source_model_mono (actual upper : RationalCostModel) (h : ∀ n,actual.rat n≤upper.rat n) (W m k Qv : ℕ) :
    sourceProfile actual W m k Qv≤sourceProfile upper W m k Qv :=
  Nat.add_le_add (Nat.add_le_add (initial_model_mono actual upper h W m k)
    (GeneralPaperScoreResidencyRates.threshold_mono actual upper h W m k))
    (GeneralPaperGuardMinimumStorageRates.guard_mono actual upper h W m k Qv)

def certificate (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    Certificate (fun x => sourceProfile (GeneralPaperFastRationalMajorant.model C d) (W x) x.m x.k x.Qv) := by
  refine ⟨3,0,2,?_⟩
  exact GeneralPaperSourceRateAlgebra.add _ _ 3 0 2 3 0 2
    (GeneralPaperSourceRateAlgebra.add _ _ 2 0 2 3 0 2 (initialCertificate C d W hW).bound (thresholdCertificate C d W hW).bound)
    (guardCertificate C d W hW).bound

theorem degrees (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    ((certificate C d W hW).fields,(certificate C d W hW).symbols,(certificate C d W hW).accuracy)=(3,0,2) := rfl

def reservation (model : RationalCostModel) (W m k Qv : ℕ) : ℕ := GeneralPaperSourceStrictConstructorStorageRates.reservation model W m k Qv+sourceProfile model W m k Qv

def reservationCertificate (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    Certificate (fun x => reservation (GeneralPaperFastRationalMajorant.model C d) (W x) x.m x.k x.Qv) := by
  refine ⟨3,0,4,?_⟩
  exact GeneralPaperSourceRateAlgebra.add _ _ 3 0 4 3 0 2
    (GeneralPaperSourceStrictConstructorStorageRates.reservationCertificate C d W hW).bound (certificate C d W hW).bound

theorem reservation_degrees (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    ((reservationCertificate C d W hW).fields,(reservationCertificate C d W hW).symbols,(reservationCertificate C d W hW).accuracy)=(3,0,4) := rfl

theorem reservation_scaling (model : RationalCostModel) (m k Qv : ℕ) : GeneralPaperReferenceScaling.Scale (fun W => reservation model W m k Qv) := by
  have hOld := GeneralPaperSourceStrictConstructorStorageRates.reservation_scaling model m k Qv
  have hNew := source_scaling model m k Qv
  unfold reservation
  fun_prop

theorem reservation_mono (actual upper : RationalCostModel) (h : ∀ n,actual.rat n≤upper.rat n) (W m k Qv : ℕ) :
    reservation actual W m k Qv≤reservation upper W m k Qv :=
  Nat.add_le_add (GeneralPaperSourceStrictConstructorStorageRates.reservation_mono actual upper h W m k Qv) (source_model_mono actual upper h W m k Qv)

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

end Blotto.GeneralPaperSourceStrictChildStorageRates
