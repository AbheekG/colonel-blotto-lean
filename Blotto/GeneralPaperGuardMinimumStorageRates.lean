import Blotto.GeneralPaperSourceGuardStorage
import Blotto.GeneralPaperHighMinimumStorage
import Blotto.GeneralPaperScoreEntryStorageRates

/-! Source terminal-guard storage has the same soft degree as its retained
DP table. The separate high-minimum profile is bounded parametrically in a
proved operand envelope; instantiation with actual ray states is a later
join. All height/growth conditions here are erased analytical properties. -/
namespace Blotto.GeneralPaperGuardMinimumStorageRates
open GeneralPaperSourceWordGrowth GeneralPaperSourceSoftBounds GeneralPaperSourceRateAlgebra
open GeneralPaperCompilerReferenceGrowth GeneralPaperConstructedWordGrowth
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192

def guardCertificate (C d : ℕ) (W : Input → ℕ) (hW : Tight W) : Certificate (fun x =>
    GeneralPaperSourceGuardStorage.sourceProfile (GeneralPaperFastRationalMajorant.model C d) (W x) x.m x.k x.Qv) := by
  have hr : Rated W 0 0 0 := poly (poly_tight W hW)
  have hs := of_tight hW
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
    ((guardCertificate C d W hW).fields,(guardCertificate C d W hW).symbols,(guardCertificate C d W hW).accuracy)=(2,1,1) := rfl

theorem guard_scaling (model : RationalCostModel) (m k Qv : ℕ) :
    GeneralPaperReferenceScaling.Scale (fun W => GeneralPaperSourceGuardStorage.sourceProfile model W m k Qv) := by
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
  fun_prop

theorem guard_mono (actual upper : RationalCostModel) (h : ∀ n,actual.rat n≤upper.rat n) (W m k Qv : ℕ) :
    GeneralPaperSourceGuardStorage.sourceProfile actual W m k Qv≤GeneralPaperSourceGuardStorage.sourceProfile upper W m k Qv := by
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
  gcongr <;> exact h _

theorem actual_guard_rate {actual : RationalCostModel} {C d : ℕ}
    (hg : GeneralPaperFastRationalModel.Growth actual C d) (W : Input → ℕ) (hW : Tight W) : Rated (fun x =>
    GeneralPaperSourceGuardStorage.sourceProfile actual (W x) x.m x.k x.Qv) 2 1 1 :=
  GeneralPaperSourceSoftBounds.dominated (guardCertificate C d W hW).bound
    (fun x => guard_mono actual (GeneralPaperFastRationalMajorant.model C d)
      (GeneralPaperFastRationalMajorant.dominates hg) (W x) x.m x.k x.Qv)

theorem guard_at_one_small (C d : ℕ) : Small (fun x =>
    GeneralPaperSourceGuardStorage.sourceProfile (GeneralPaperFastRationalMajorant.model C d) 1 x.m x.k x.Qv) := by
  apply GeneralPaperSourceRowsStorageRates.soft_small (guardCertificate C d (fun _ => 1) (tight_constant 1)).bound
  unfold monomial GeneralPaperNativeSourceRates.fields GeneralPaperNativeSourceRates.symbols GeneralPaperNativeSourceRates.accuracy
  fun_prop

theorem actual_guard_common_word {actual : RationalCostModel} {C d : ℕ}
    (hg : GeneralPaperFastRationalModel.Growth actual C d) : ∃ A e : ℕ,∀ x,
    GeneralPaperSourceGuardStorage.sourceProfile actual (GeneralPaperCompilerReference.width C d x) x.m x.k x.Qv≤
      A*monomial 2 1 1 x*(logSize x)^e := actual_guard_rate hg _ (width_tight C d)

def highCertificate (C d : ℕ) (W A : Input → ℕ) (hW : Tight W) (hA : Rated A 1 1 1) (hsA : Small A) :
    Certificate (fun x => GeneralPaperHighMinimumStorage.profile (GeneralPaperFastRationalMajorant.model C d)
      (W x) (GeneralPaperProxyParameters.prepare x.m x.k).K (GeneralPaperProxyParameters.prepare x.m x.k).S (A x) x.m) := by
  have hr : Rated W 0 0 0 := poly (poly_tight W hW)
  have hs := of_tight hW
  refine ⟨_,_,_,by
    unfold GeneralPaperHighMinimumStorage.profile GeneralPaperHighMinimumStorage.metadataCap
      GeneralPaperHighMinimumStorage.workCap GeneralPaperScoreLifetimeStorage.workCap
      GeneralPaperIndexedMinimumStorage.profile GeneralPaperIndexedMinimumStorage.frameProfile GeneralPaperIndexedMinimumStorage.workCap
      GeneralPaperScoreTableStorage.tableProfile GeneralPaperScoreSelectionStorage.optionProfile GeneralPaperScoreSelectionStorage.selectionProfile
      GeneralPaperScoreDPBits.profile GeneralPaperScoreDPBits.stepProfile GeneralPaperScoreDPBits.initialProfile
      GeneralPaperScoreBitPrimitive.resourceWidth GeneralPaperEncodedScalarStorage.natBits
    dsimp only [GeneralPaperFastRationalMajorant.model]
    source_space⟩

theorem high_degrees (C d : ℕ) (W A : Input → ℕ) (hW : Tight W) (hA : Rated A 1 1 1) (hsA : Small A) :
    ((highCertificate C d W A hW hA hsA).fields,(highCertificate C d W A hW hA hsA).symbols,
      (highCertificate C d W A hW hA hsA).accuracy)=(3,1,2) := rfl

theorem high_scaling (model : RationalCostModel) (K S A r : ℕ) :
    GeneralPaperReferenceScaling.Scale (fun W => GeneralPaperHighMinimumStorage.profile model W K S A r) := by
  unfold GeneralPaperHighMinimumStorage.profile GeneralPaperHighMinimumStorage.metadataCap
      GeneralPaperHighMinimumStorage.workCap GeneralPaperScoreLifetimeStorage.workCap
      GeneralPaperIndexedMinimumStorage.profile GeneralPaperIndexedMinimumStorage.frameProfile GeneralPaperIndexedMinimumStorage.workCap
      GeneralPaperScoreTableStorage.tableProfile GeneralPaperScoreSelectionStorage.optionProfile GeneralPaperScoreSelectionStorage.selectionProfile
      GeneralPaperScoreDPBits.profile GeneralPaperScoreDPBits.stepProfile GeneralPaperScoreDPBits.initialProfile
      GeneralPaperScoreBitPrimitive.resourceWidth GeneralPaperEncodedScalarStorage.natBits
  dsimp only
  fun_prop

theorem high_mono (actual upper : RationalCostModel) (h : ∀ n,actual.rat n≤upper.rat n) (W K S A r : ℕ) :
    GeneralPaperHighMinimumStorage.profile actual W K S A r≤GeneralPaperHighMinimumStorage.profile upper W K S A r := by
  unfold GeneralPaperHighMinimumStorage.profile GeneralPaperHighMinimumStorage.metadataCap
      GeneralPaperHighMinimumStorage.workCap GeneralPaperScoreLifetimeStorage.workCap
      GeneralPaperIndexedMinimumStorage.profile GeneralPaperIndexedMinimumStorage.frameProfile GeneralPaperIndexedMinimumStorage.workCap
      GeneralPaperScoreTableStorage.tableProfile GeneralPaperScoreSelectionStorage.optionProfile GeneralPaperScoreSelectionStorage.selectionProfile
      GeneralPaperScoreDPBits.profile GeneralPaperScoreDPBits.stepProfile GeneralPaperScoreDPBits.initialProfile
      GeneralPaperScoreBitPrimitive.resourceWidth GeneralPaperEncodedScalarStorage.natBits
  dsimp only
  gcongr <;> exact h _

theorem actual_high_rate {actual : RationalCostModel} {C d : ℕ}
    (hg : GeneralPaperFastRationalModel.Growth actual C d) (W A : Input → ℕ)
    (hW : Tight W) (hA : Rated A 1 1 1) (hsA : Small A) : Rated (fun x =>
    GeneralPaperHighMinimumStorage.profile actual (W x) (GeneralPaperProxyParameters.prepare x.m x.k).K
      (GeneralPaperProxyParameters.prepare x.m x.k).S (A x) x.m) 3 1 2 :=
  GeneralPaperSourceSoftBounds.dominated (highCertificate C d W A hW hA hsA).bound
    (fun x => high_mono actual (GeneralPaperFastRationalMajorant.model C d) (GeneralPaperFastRationalMajorant.dominates hg)
      (W x) _ _ (A x) x.m)

end Blotto.GeneralPaperGuardMinimumStorageRates

