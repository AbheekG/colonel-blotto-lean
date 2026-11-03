import Blotto.GeneralPaperSourceSharpOperandRates

/-! The unchanged complete per-query owner/predicate profile has sharper
soft degree (3,0,2) for the actual selected source. All previously checked
native windows therefore inherit this bound. Global search/compiler space
and original-input joins remain separate requirements. -/
namespace Blotto.GeneralPaperSourceSharpOwnerRates
open GeneralPaperSourceWordGrowth GeneralPaperSourceSoftBounds GeneralPaperSourceRateAlgebra
open GeneralPaperConstructedWordGrowth GeneralPaperCompilerReferenceGrowth
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxRecDepth 8192

def certificate (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    Certificate (fun x => GeneralPaperSourceEndpointOwnerStorage.profile (GeneralPaperFastRationalMajorant.model C d) (W x) x.m x.k) := by
  have hr : Rated W 0 0 0 := poly (poly_tight W hW)
  have hs := of_tight hW
  have hR := GeneralPaperSourceSharpOperandRates.ray_width
  have hAnchor := GeneralPaperSourceSharpOperandRates.anchor_height
  have hsR := GeneralPaperSourceRayStorageRates.width_small
  refine ⟨_,_,_,by
    unfold GeneralPaperSourceEndpointOwnerStorage.profile GeneralPaperSourceRayQueryOwners.profile GeneralPaperSourceRayQueryOwners.preparationPrice
      GeneralPaperRayPredicateStorage.profile GeneralPaperRayPredicateStorage.metadataCap GeneralPaperRayPredicateStorage.price GeneralPaperRayPredicateStorage.minimumPrice
      GeneralPaperRayQueryStorageEnvelope.profile GeneralPaperRayQueryStorageEnvelope.frameProfile GeneralPaperRayQueryStorageEnvelope.constructionProfile
      GeneralPaperRayQueryStorageEnvelope.costProfile GeneralPaperRayQueryStorageEnvelope.minimumProfile GeneralPaperEncodedRationalRows.rowProfile
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
    ((certificate C d W hW).fields,(certificate C d W hW).symbols,(certificate C d W hW).accuracy)=(3,0,2) := rfl

theorem actual_rate {actual : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth actual C d)
    (W : Input → ℕ) (hW : Tight W) : Rated (fun x =>
    GeneralPaperSourceEndpointOwnerStorage.profile actual (W x) x.m x.k) 3 0 2 :=
  GeneralPaperSourceSoftBounds.dominated (certificate C d W hW).bound
    (fun x => GeneralPaperSourceEndpointOwnerRates.model_mono actual (GeneralPaperFastRationalMajorant.model C d) (GeneralPaperFastRationalMajorant.dominates hg) (W x) x.m x.k)

theorem at_one_small (C d : ℕ) : Small (fun x =>
    GeneralPaperSourceEndpointOwnerStorage.profile (GeneralPaperFastRationalMajorant.model C d) 1 x.m x.k) := by
  apply GeneralPaperSourceRowsStorageRates.soft_small (certificate C d (fun _ => 1) (tight_constant 1)).bound
  unfold monomial GeneralPaperNativeSourceRates.fields GeneralPaperNativeSourceRates.symbols GeneralPaperNativeSourceRates.accuracy
  fun_prop

theorem actual_common_word {actual : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth actual C d) :
    ∃ A e : ℕ,∀ x,GeneralPaperSourceEndpointOwnerStorage.profile actual (GeneralPaperCompilerReference.width C d x) x.m x.k≤
      A*monomial 3 0 2 x*(logSize x)^e := actual_rate hg _ (width_tight C d)

end Blotto.GeneralPaperSourceSharpOwnerRates

