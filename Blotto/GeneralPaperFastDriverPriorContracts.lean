import Blotto.GeneralPaperFastDriverReferenceContract

/-! The enlarged whole-driver reference preserves the original reached
controller, simultaneous physical owners and reciprocal-zero guard path.
Only the closed enclosing reference changes; the selected source, strict
lower-score DP, compiler branches and native returns remain identical. -/
namespace Blotto.GeneralPaperFastDriverPriorContracts
open GeneralPaperSourceWordGrowth GeneralPaperFastDriverReference GeneralPaperProxyParameters
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 16384

theorem reached_controller {model : RationalCostModel} {C d : ℕ}
    (hg : GeneralPaperFastRationalModel.Growth model C d) :
    ∀ z : Input,
      let W := width C d z
      ∀ (_hm : 0<z.m) (hQv : 0<z.Qv) (hp : ∀ j,0<z.weights.read j)
        (b : ℝ) (_hb : 0<b ∧ b<1) (reciprocal : Bool)
        (_hModify : (GeneralPaperProxyClassifier.classify z.m z.k b).choice.modify≠none)
        (_hGuard : ¬(reciprocal=true ∧ (GeneralPaperProxyClassifier.classify z.m z.k b).choice.endpoint=0)),
        let prep := GeneralPaperSourceInitializer.prepared z.k z.Qv hQv z.weights hp z.weight_sum b reciprocal
        let v := GeneralPaperNativeRationalValues.selector z.Qv hQv z.weights hp z.weight_sum
        let f := (GeneralPaperProxyClassifier.classify z.m z.k b).choice.proxy
        let inputs := GeneralPaperSharedBasisInputs.prepare z.k prep v f.num f.den reciprocal
        ∃ state,(GeneralPaperBasisControllerBits.stages model W prep.dictionary.label inputs.matrix (prepare z.m z.k).S prep.threshold
          inputs.controls.N inputs.betaN inputs.initialGrid (z.m*((prepare z.m z.k).K-1)) le_rfl).1=some state ∧
          GeneralPaperSourceModifiedColumnStorage.AtBound
            (fun constructionBound => GeneralPaperSourceCompilerBranchStorage.AtBound
              (fun compilerBound => GeneralPaperSourceColumnCallerStorage.AtBound
              (fun bound => GeneralPaperSourceRowsCallerStorage.AtBound
              (fun limit => GeneralPaperSourceUnitCallerStorage.AtBound model W z.k limit b reciprocal prep inputs state
            (GeneralPaperSourceEnclosingOwners.window model W z.k z.Qv hQv z.weights hp z.weight_sum b reciprocal)
            (GeneralPaperSourceStrictConstructorStorage.parentWindow model W z.k z.Qv hQv z.weights hp z.weight_sum b reciprocal)
            (GeneralPaperSourceEnclosingOwners.columns model W z.k z.Qv z.weights b reciprocal)
            (GeneralPaperRetainedFieldValues.run true model W z.Qv hQv z.weights hp z.weight_sum).1
            (GeneralPaperInitializerPreparedPoint.ownBudget z.m z.k b reciprocal) (GeneralPaperInitializerPreparedPoint.opposingBudget z.m z.k b reciprocal)
            (GeneralPaperSourceDictionaryNormalizationStorage.quantized model W z.k z.Qv z.weights b reciprocal)
            (GeneralPaperSourceQuantizedAnchorStorage.window model W z.k z.Qv z.weights b reciprocal)
            (GeneralPaperSourceRepresentativeSortStorage.window model W z.k z.Qv z.weights b reciprocal)
            (GeneralPaperSourceColumnInputStorage.window model W z.k z.Qv z.weights b reciprocal)
            (GeneralPaperSourceBlockDivisionStorage.window model W z.m z.k)
            (GeneralPaperSourceLabelScatterStorage.window model W z.k z.Qv z.weights b reciprocal)
            (GeneralPaperSourceQuantizationParentStorage.window model W z.k z.Qv z.weights b reciprocal)
            (GeneralPaperSourceUnitCallerStorage.window model W z.k z.Qv z.weights b reciprocal))
            (GeneralPaperSourceRowsCallerStorage.window model W z.k z.Qv z.weights b reciprocal) bound)
            (GeneralPaperSourceColumnCallerStorage.window model W z.k z.Qv z.weights b reciprocal) compilerBound)
            (GeneralPaperSourceCompilerBranchStorage.window model W z.k z.Qv hQv z.weights hp z.weight_sum b reciprocal) constructionBound)
            (GeneralPaperSourceModifiedColumnStorage.window model W z.k z.Qv hQv z.weights hp z.weight_sum b reciprocal)
            (profile C d W z) := by
  intro z
  dsimp only
  intro hm hQv hp b hb reciprocal hModify hGuard
  let W := width C d z
  have hw := positive_width C d z
  have h := local_words C d z
  have hr := row_words C d z
  have hTop := (modified_reserve_le model C d W z.m z.k z.Qv z.B).trans
    (actual_reserve hg W z)
  obtain ⟨state,hNative,hBound⟩ := GeneralPaperSourceModifiedColumnStorage.actual_reached hg W z.k z.Qv hm hQv z.weights hp z.weight_sum b hb reciprocal hModify hGuard
    hw h.2.1 h.2.2.1 h.2.2.2.1 h.1 h.2.2.2.2.1 hr.1 hr.2 h.2.2.2.2.2.1
  refine ⟨state,hNative,?_⟩
  exact GeneralPaperSourceModifiedColumnStorage.bound_mono _ _ _ _ hTop hBound

theorem guard_lifetimes {model : RationalCostModel} {C d : ℕ}
    (hg : GeneralPaperFastRationalModel.Growth model C d) :
    ∀ z : Input,
      let W := width C d z
      ∀ (_hm : 0<z.m) (hQv : 0<z.Qv) (hp : ∀ j,0<z.weights.read j)
        (b : ℝ) (_hb : 0<b ∧ b<1) (reciprocal : Bool)
        (_hModify : (GeneralPaperProxyClassifier.classify z.m z.k b).choice.modify≠none)
        (_hGuard : reciprocal=true ∧ (GeneralPaperProxyClassifier.classify z.m z.k b).choice.endpoint=0),
        let prep := GeneralPaperSourceInitializer.prepared z.k z.Qv hQv z.weights hp z.weight_sum b reciprocal
        let v := GeneralPaperNativeRationalValues.selector z.Qv hQv z.weights hp z.weight_sum
        let f := (GeneralPaperProxyClassifier.classify z.m z.k b).choice.proxy
        let inputs := GeneralPaperSharedBasisInputs.prepare z.k prep v f.num f.den reciprocal
        GeneralPaperSourceOuterEndpointStorage.window model W z.k b reciprocal prep inputs+
          GeneralPaperSourceEndpointFractionConstructionStorage.window model W z.m z.k b+
          GeneralPaperSourceEnclosingOwners.window model W z.k z.Qv hQv z.weights hp z.weight_sum b reciprocal+
          GeneralPaperSourceStrictConstructorStorage.parentWindow model W z.k z.Qv hQv z.weights hp z.weight_sum b reciprocal+
          GeneralPaperSourceMatrixStorage.sourceProfile model W z.m z.k z.Qv+GeneralPaperSourceScoreStorage.profile model W z.m z.k+
          GeneralPaperScoreResidencyRates.initialProfile model W z.m z.k+GeneralPaperSourceScoreResidents.thresholdProfile model W z.m z.k+
          GeneralPaperSourceGuardStorage.sourceProfile model W z.m z.k z.Qv+
          GeneralPaperSourceDictionaryNormalizationStorageRates.sourceProfile model W z.m z.k+
          GeneralPaperSourceQuantizedAnchorStorageRates.sourceProfile model W z.m z.k+
          GeneralPaperSourceRepresentativeSortStorageRates.sourceProfile model W z.m z.k+
          GeneralPaperSourceColumnInputStorageRates.sourceProfile model W z.m z.k+
          GeneralPaperSourceBlockDivisionStorageRates.sourceProfile model W z.m z.k+
          GeneralPaperSourceLabelScatterStorageRates.sourceProfile model W z.m z.k+
          GeneralPaperSourceQuantizationParentStorageRates.sourceProfile model W z.m z.k+
          GeneralPaperSourceUnitCallerStorageRates.sourceProfile model W z.m z.k+
          GeneralPaperSourceRowsCallerStorageRates.sourceProfile C d W z.m z.k z.Qv+
          GeneralPaperSourceColumnCallerStorageRates.sourceProfile model C d W z.m z.k z.Qv+
          GeneralPaperSourceCompilerBranchStorageRates.sourceProfile model W z.m z.k z.Qv+
          GeneralPaperSourceModifiedColumnStorageRates.sourceProfile model W z.m z.k z.Qv≤
            profile C d W z := by
  intro z
  dsimp only
  intro hm hQv hp b hb reciprocal hModify hGuard
  let W := width C d z
  have hw := positive_width C d z
  have h := local_words C d z
  have hr := row_words C d z
  have hTop := (modified_reserve_le model C d W z.m z.k z.Qv z.B).trans
    (actual_reserve hg W z)
  exact (GeneralPaperSourceModifiedColumnStorage.guard_stage model C d W z.k z.Qv hm hQv z.weights hp z.weight_sum b hb reciprocal hModify hGuard
    hw h.2.1 h.2.2.1 h.2.2.2.1).trans hTop


end Blotto.GeneralPaperFastDriverPriorContracts
