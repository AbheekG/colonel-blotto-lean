import Blotto.GeneralPaperSourceScoreResidents

/-! Parameter growth for matrix residency, its constructor reservations,
initial-table residency and the strict scan over the retained source table.
Original input budget height enters none of these repeated phase profiles.
Entry-arithmetic, stored-maximum/high-minimum and final global joins remain
separate; positive scaling does not assert final address coverage. -/
namespace Blotto.GeneralPaperScoreResidencyRates
open GeneralPaperSourceWordGrowth GeneralPaperSourceSoftBounds GeneralPaperSourceRateAlgebra
open GeneralPaperCompilerReferenceGrowth GeneralPaperConstructedWordGrowth
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192

@[fun_prop]
theorem cap_small : Small (fun x => binaryWordWidth (GeneralPaperProxyParameters.prepare x.m x.k).qbar) := by
  apply GeneralPaperSourceWordGrowth.dominated (g:=fun x => (alphabet x).lambda+1)
  · fun_prop
  · intro x
    exact GeneralPaperSourceBudgetWidths.cap_height x.m x.k

@[fun_prop]
theorem depth_small : Small (fun x => (GeneralPaperScoreScaleParameters.prepare x.m x.k).depth) := by
  apply GeneralPaperSourceWordGrowth.dominated (g:=fun x => binaryWordWidth (x.m*(GeneralPaperProxyParameters.prepare x.m x.k).K)+1)
  · fun_prop
  · intro x
    exact GeneralPaperScoreScaleParameters.depth_bound x.m x.k

def residentCertificate (W : Input → ℕ) (hW : Tight W) : Certificate (fun x =>
    GeneralPaperSourceScoreResidents.residentProfile (W x) x.m x.k) := by
  have hr : Rated W 0 0 0 := poly (poly_tight W hW)
  refine ⟨_,_,_,by
    unfold GeneralPaperSourceScoreResidents.residentProfile GeneralPaperScoreResidentPhases.residentProfile
      GeneralPaperEncodedScoreMatrixStorage.matrixProfile GeneralPaperEncodedScoreMatrixStorage.fieldProfile
      GeneralPaperEncodedScoreMatrixStorage.entryProfile GeneralPaperEncodedScalarStorage.natBits
    source_space⟩

theorem resident_degrees (W : Input → ℕ) (hW : Tight W) :
    ((residentCertificate W hW).fields,(residentCertificate W hW).symbols,(residentCertificate W hW).accuracy)=(1,1,1) := rfl

def constructionProfile (model : RationalCostModel) (W m k Qv : ℕ) : ℕ :=
  GeneralPaperScoreMatrixConstructionStorage.profile model W (GeneralPaperScoreScaleParameters.prepare m k).depth
    (GeneralPaperProxyParameters.prepare m k).S (binaryWordWidth Qv) (GeneralPaperSourceScoreHeights.anchorHeight m k)
    m (GeneralPaperProxyParameters.prepare m k).K

def constructionCertificate (C d : ℕ) (W : Input → ℕ) (hW : Tight W) : Certificate (fun x =>
    constructionProfile (GeneralPaperFastRationalMajorant.model C d) (W x) x.m x.k x.Qv) := by
  have hr : Rated W 0 0 0 := poly (poly_tight W hW)
  have hs := of_tight hW
  refine ⟨_,_,_,by
    unfold constructionProfile GeneralPaperScoreMatrixConstructionStorage.profile
      GeneralPaperEncodedScoreMatrixStorage.matrixProfile GeneralPaperEncodedScoreMatrixStorage.fieldProfile
      GeneralPaperEncodedScoreMatrixStorage.entryProfile GeneralPaperScoreConstructionStorage.constructorProfile
      GeneralPaperScoreMatrixBits.matrixProfile GeneralPaperScoreMatrixBits.fieldProfile GeneralPaperScoreMatrixBits.entryProfile
      GeneralPaperScoreMatrixBits.scoreProfile GeneralPaperScoreArgumentBits.argumentProfile GeneralPaperScoreArgumentBits.height
      GeneralPaperBoundedQuotient.bitProfile GeneralPaperBoundedQuotient.heightBudget GeneralPaperEncodedScalarStorage.natBits
    dsimp only [GeneralPaperFastRationalMajorant.model]
    source_space⟩

theorem construction_degrees (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    ((constructionCertificate C d W hW).fields,(constructionCertificate C d W hW).symbols,
      (constructionCertificate C d W hW).accuracy)=(1,1,1) := rfl

def initialProfile (model : RationalCostModel) (W m k : ℕ) : ℕ :=
  let p := GeneralPaperProxyParameters.prepare m k
  GeneralPaperSourceScoreResidents.residentProfile W m k+
    GeneralPaperScoreLifetimeStorage.callerProfile model W p.K p.S (GeneralPaperSourceScoreHeights.anchorHeight m k) m+
    GeneralPaperScoreInitialStorage.profile W p.K p.S

def initialCertificate (C d : ℕ) (W : Input → ℕ) (hW : Tight W) : Certificate (fun x =>
    initialProfile (GeneralPaperFastRationalMajorant.model C d) (W x) x.m x.k) := by
  have hr : Rated W 0 0 0 := poly (poly_tight W hW)
  have hs := of_tight hW
  refine ⟨_,_,_,by
    unfold initialProfile GeneralPaperSourceScoreResidents.residentProfile GeneralPaperScoreResidentPhases.residentProfile
      GeneralPaperEncodedScoreMatrixStorage.matrixProfile GeneralPaperEncodedScoreMatrixStorage.fieldProfile
      GeneralPaperEncodedScoreMatrixStorage.entryProfile GeneralPaperScoreInitialStorage.profile
      GeneralPaperScoreTableStorage.tableProfile GeneralPaperScoreSelectionStorage.optionProfile
      GeneralPaperScoreSelectionStorage.selectionProfile GeneralPaperScoreConstructionStorage.constructorProfile
      GeneralPaperScoreLifetimeStorage.callerProfile GeneralPaperScoreLifetimeStorage.workCap
      GeneralPaperScoreDPBits.profile GeneralPaperScoreDPBits.initialProfile GeneralPaperScoreDPBits.stepProfile
      GeneralPaperScoreBitPrimitive.resourceWidth GeneralPaperEncodedScalarStorage.natBits
    dsimp only [GeneralPaperFastRationalMajorant.model]
    source_space⟩

theorem initial_degrees (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    ((initialCertificate C d W hW).fields,(initialCertificate C d W hW).symbols,(initialCertificate C d W hW).accuracy)=(1,1,1) := rfl

def thresholdCertificate (C d : ℕ) (W : Input → ℕ) (hW : Tight W) : Certificate (fun x =>
    GeneralPaperSourceScoreResidents.thresholdProfile (GeneralPaperFastRationalMajorant.model C d) (W x) x.m x.k) := by
  have hr : Rated W 0 0 0 := poly (poly_tight W hW)
  have hs := of_tight hW
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

theorem threshold_degrees (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    ((thresholdCertificate C d W hW).fields,(thresholdCertificate C d W hW).symbols,(thresholdCertificate C d W hW).accuracy)=(2,1,1) := rfl

theorem threshold_scaling (model : RationalCostModel) (m k : ℕ) : GeneralPaperReferenceScaling.Scale (fun W =>
    GeneralPaperSourceScoreResidents.thresholdProfile model W m k) := by
  unfold GeneralPaperSourceScoreResidents.thresholdProfile GeneralPaperScoreResidentPhases.thresholdProfile
    GeneralPaperThresholdScanStorage.profile GeneralPaperThresholdScanStorage.frameProfile GeneralPaperThresholdScanStorage.cap
  fun_prop

theorem threshold_mono (actual upper : RationalCostModel) (h : ∀ n,actual.rat n≤upper.rat n) (W m k : ℕ) :
    GeneralPaperSourceScoreResidents.thresholdProfile actual W m k≤GeneralPaperSourceScoreResidents.thresholdProfile upper W m k := by
  unfold GeneralPaperSourceScoreResidents.thresholdProfile GeneralPaperScoreResidentPhases.thresholdProfile
    GeneralPaperThresholdScanStorage.profile GeneralPaperThresholdScanStorage.frameProfile GeneralPaperThresholdScanStorage.cap
    GeneralPaperEncodedScalarStorage.natBits
  gcongr <;> exact h _

theorem actual_threshold_rate {actual : RationalCostModel} {C d : ℕ}
    (hg : GeneralPaperFastRationalModel.Growth actual C d) (W : Input → ℕ) (hW : Tight W) : Rated (fun x =>
    GeneralPaperSourceScoreResidents.thresholdProfile actual (W x) x.m x.k) 2 1 1 :=
  GeneralPaperSourceSoftBounds.dominated (thresholdCertificate C d W hW).bound
    (fun x => threshold_mono actual (GeneralPaperFastRationalMajorant.model C d)
      (GeneralPaperFastRationalMajorant.dominates hg) (W x) x.m x.k)

theorem threshold_at_one_small (C d : ℕ) : Small (fun x =>
    GeneralPaperSourceScoreResidents.thresholdProfile (GeneralPaperFastRationalMajorant.model C d) 1 x.m x.k) := by
  apply GeneralPaperSourceRowsStorageRates.soft_small (thresholdCertificate C d (fun _ => 1) (tight_constant 1)).bound
  unfold monomial GeneralPaperNativeSourceRates.fields GeneralPaperNativeSourceRates.symbols GeneralPaperNativeSourceRates.accuracy
  fun_prop

theorem actual_common_word_bound {actual : RationalCostModel} {C d : ℕ}
    (hg : GeneralPaperFastRationalModel.Growth actual C d) : ∃ A e : ℕ,∀ x,
    GeneralPaperSourceScoreResidents.thresholdProfile actual (GeneralPaperCompilerReference.width C d x) x.m x.k≤
      A*monomial 2 1 1 x*(logSize x)^e := actual_threshold_rate hg _ (width_tight C d)

end Blotto.GeneralPaperScoreResidencyRates
