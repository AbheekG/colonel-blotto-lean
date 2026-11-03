import Blotto.GeneralPaperSourceRayQueryStorage

/-! The source-wide ray operand family and resulting complete local query
storage have explicit soft rates, without caller height-family premises.
This is not yet the enclosing high-search or global compiler-space bound. -/
namespace Blotto.GeneralPaperSourceRayStorageRates
open GeneralPaperSourceWordGrowth GeneralPaperSourceSoftBounds GeneralPaperSourceRateAlgebra
open GeneralPaperConstructedWordGrowth GeneralPaperCompilerReferenceGrowth
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxRecDepth 8192

@[fun_prop]
theorem width_rate : Rated (fun x => GeneralPaperSourceRayStorageWidth.width x.m x.k) 1 1 1 := by
  unfold GeneralPaperSourceRayStorageWidth.width GeneralPaperSourceRayStorageWidth.rootWidth GeneralPaperSourceRayStorageWidth.gridWord
  source_space

@[fun_prop]
theorem width_small : Small (fun x => GeneralPaperSourceRayStorageWidth.width x.m x.k) := by
  apply GeneralPaperSourceRowsStorageRates.soft_small width_rate
  unfold monomial GeneralPaperNativeSourceRates.fields GeneralPaperNativeSourceRates.symbols GeneralPaperNativeSourceRates.accuracy
  fun_prop

theorem scaling (model : RationalCostModel) (m k : ℕ) :
    GeneralPaperReferenceScaling.Scale (fun W => GeneralPaperSourceRayQueryStorage.profile model W m k) := by
  unfold GeneralPaperSourceRayQueryStorage.profile GeneralPaperRayQueryStorageEnvelope.profile
      GeneralPaperRayQueryStorageEnvelope.frameProfile GeneralPaperRayQueryStorageEnvelope.constructionProfile
      GeneralPaperRayQueryStorageEnvelope.costProfile GeneralPaperRayQueryStorageEnvelope.minimumProfile
      GeneralPaperRayMinimumBits.profile GeneralPaperHighMinimumStorage.profile GeneralPaperHighMinimumStorage.metadataCap GeneralPaperHighMinimumStorage.workCap
      GeneralPaperIndexedMinimumStorage.profile GeneralPaperIndexedMinimumStorage.frameProfile GeneralPaperIndexedMinimumStorage.workCap
      GeneralPaperScoreLifetimeStorage.layerProfile GeneralPaperScoreLifetimeStorage.callerProfile GeneralPaperScoreLifetimeStorage.workCap
      GeneralPaperScoreConstructionStorage.stepProfile GeneralPaperScoreConstructionStorage.constructorProfile
      GeneralPaperScoreScanStorage.profile GeneralPaperScoreScanStorage.frameProfile GeneralPaperScoreScanStorage.workCap
      GeneralPaperScoreInitialStorage.profile GeneralPaperEncodedScoreMatrixStorage.matrixProfile GeneralPaperEncodedScoreMatrixStorage.fieldProfile
      GeneralPaperEncodedScoreMatrixStorage.entryProfile GeneralPaperScoreTableStorage.tableProfile GeneralPaperScoreSelectionStorage.optionProfile
      GeneralPaperScoreSelectionStorage.selectionProfile GeneralPaperCommonLatticeMinimumBits.profile GeneralPaperScoreDPBits.profile
      GeneralPaperScoreDPBits.stepProfile GeneralPaperScoreDPBits.initialProfile GeneralPaperScoreBitPrimitive.resourceWidth
      GeneralPaperEncodedScalarStorage.natBits
  unfold GeneralPaperScoreConstructionStorage.constructorProfile GeneralPaperEncodedScalarStorage.natBits
  dsimp only
  fun_prop

theorem model_mono (actual upper : RationalCostModel) (h : ∀ n,actual.rat n≤upper.rat n) (W m k : ℕ) :
    GeneralPaperSourceRayQueryStorage.profile actual W m k≤GeneralPaperSourceRayQueryStorage.profile upper W m k := by
  unfold GeneralPaperSourceRayQueryStorage.profile GeneralPaperRayQueryStorageEnvelope.profile
      GeneralPaperRayQueryStorageEnvelope.frameProfile GeneralPaperRayQueryStorageEnvelope.constructionProfile
      GeneralPaperRayQueryStorageEnvelope.costProfile GeneralPaperRayQueryStorageEnvelope.minimumProfile
      GeneralPaperRayMinimumBits.profile GeneralPaperHighMinimumStorage.profile GeneralPaperHighMinimumStorage.metadataCap GeneralPaperHighMinimumStorage.workCap
      GeneralPaperIndexedMinimumStorage.profile GeneralPaperIndexedMinimumStorage.frameProfile GeneralPaperIndexedMinimumStorage.workCap
      GeneralPaperScoreLifetimeStorage.layerProfile GeneralPaperScoreLifetimeStorage.callerProfile GeneralPaperScoreLifetimeStorage.workCap
      GeneralPaperScoreConstructionStorage.stepProfile GeneralPaperScoreConstructionStorage.constructorProfile
      GeneralPaperScoreScanStorage.profile GeneralPaperScoreScanStorage.frameProfile GeneralPaperScoreScanStorage.workCap
      GeneralPaperScoreInitialStorage.profile GeneralPaperEncodedScoreMatrixStorage.matrixProfile GeneralPaperEncodedScoreMatrixStorage.fieldProfile
      GeneralPaperEncodedScoreMatrixStorage.entryProfile GeneralPaperScoreTableStorage.tableProfile GeneralPaperScoreSelectionStorage.optionProfile
      GeneralPaperScoreSelectionStorage.selectionProfile GeneralPaperCommonLatticeMinimumBits.profile GeneralPaperScoreDPBits.profile
      GeneralPaperScoreDPBits.stepProfile GeneralPaperScoreDPBits.initialProfile GeneralPaperScoreBitPrimitive.resourceWidth
      GeneralPaperEncodedScalarStorage.natBits
  unfold GeneralPaperScoreConstructionStorage.constructorProfile GeneralPaperEncodedScalarStorage.natBits
  dsimp only
  gcongr <;> exact h _

def certificate (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    Certificate (fun x => GeneralPaperSourceRayQueryStorage.profile (GeneralPaperFastRationalMajorant.model C d) (W x) x.m x.k) := by
  have hr : Rated W 0 0 0 := poly (poly_tight W hW)
  have hs := of_tight hW
  have hR := width_rate
  have hsR := width_small
  refine ⟨_,_,_,by
    unfold GeneralPaperSourceRayQueryStorage.profile GeneralPaperRayQueryStorageEnvelope.profile
      GeneralPaperRayQueryStorageEnvelope.frameProfile GeneralPaperRayQueryStorageEnvelope.constructionProfile
      GeneralPaperRayQueryStorageEnvelope.costProfile GeneralPaperRayQueryStorageEnvelope.minimumProfile
      GeneralPaperRayMinimumBits.profile GeneralPaperHighMinimumStorage.profile GeneralPaperHighMinimumStorage.metadataCap GeneralPaperHighMinimumStorage.workCap
      GeneralPaperIndexedMinimumStorage.profile GeneralPaperIndexedMinimumStorage.frameProfile GeneralPaperIndexedMinimumStorage.workCap
      GeneralPaperScoreLifetimeStorage.layerProfile GeneralPaperScoreLifetimeStorage.callerProfile GeneralPaperScoreLifetimeStorage.workCap
      GeneralPaperScoreConstructionStorage.stepProfile GeneralPaperScoreConstructionStorage.constructorProfile
      GeneralPaperScoreScanStorage.profile GeneralPaperScoreScanStorage.frameProfile GeneralPaperScoreScanStorage.workCap
      GeneralPaperScoreInitialStorage.profile GeneralPaperEncodedScoreMatrixStorage.matrixProfile GeneralPaperEncodedScoreMatrixStorage.fieldProfile
      GeneralPaperEncodedScoreMatrixStorage.entryProfile GeneralPaperScoreTableStorage.tableProfile GeneralPaperScoreSelectionStorage.optionProfile
      GeneralPaperScoreSelectionStorage.selectionProfile GeneralPaperCommonLatticeMinimumBits.profile GeneralPaperScoreDPBits.profile
      GeneralPaperScoreDPBits.stepProfile GeneralPaperScoreDPBits.initialProfile GeneralPaperScoreBitPrimitive.resourceWidth
      GeneralPaperEncodedScalarStorage.natBits
    unfold GeneralPaperScoreConstructionStorage.constructorProfile GeneralPaperEncodedScalarStorage.natBits
    dsimp only [GeneralPaperFastRationalMajorant.model]
    source_space⟩

theorem degrees (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    ((certificate C d W hW).fields,(certificate C d W hW).symbols,(certificate C d W hW).accuracy)=(3,1,2) := rfl

theorem actual_rate {actual : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth actual C d)
    (W : Input → ℕ) (hW : Tight W) : Rated (fun x =>
    GeneralPaperSourceRayQueryStorage.profile actual (W x) x.m x.k) 3 1 2 :=
  GeneralPaperSourceSoftBounds.dominated (certificate C d W hW).bound
    (fun x => model_mono actual (GeneralPaperFastRationalMajorant.model C d) (GeneralPaperFastRationalMajorant.dominates hg) (W x) x.m x.k)

theorem at_one_small (C d : ℕ) : Small (fun x =>
    GeneralPaperSourceRayQueryStorage.profile (GeneralPaperFastRationalMajorant.model C d) 1 x.m x.k) := by
  apply GeneralPaperSourceRowsStorageRates.soft_small (certificate C d (fun _ => 1) (tight_constant 1)).bound
  unfold monomial GeneralPaperNativeSourceRates.fields GeneralPaperNativeSourceRates.symbols GeneralPaperNativeSourceRates.accuracy
  fun_prop

theorem actual_common_word {actual : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth actual C d) :
    ∃ A e : ℕ,∀ x,GeneralPaperSourceRayQueryStorage.profile actual (GeneralPaperCompilerReference.width C d x) x.m x.k≤
      A*monomial 3 1 2 x*(logSize x)^e := actual_rate hg _ (width_tight C d)

end Blotto.GeneralPaperSourceRayStorageRates

