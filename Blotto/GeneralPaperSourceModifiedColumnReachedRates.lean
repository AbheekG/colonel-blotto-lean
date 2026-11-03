import Blotto.GeneralPaperSourceModifiedColumnStorage

/-! Complete native modified-column scalar/array/caller windows join
all prior source/strict/endpoint contracts under the common paper bound. -/
namespace Blotto.GeneralPaperSourceModifiedColumnReachedRates
open GeneralPaperSourceWordGrowth GeneralPaperProxyParameters
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384

theorem actual_reached_common_word {model : RationalCostModel} {C d : ℕ}
    (hg : GeneralPaperFastRationalModel.Growth model C d) :
    ∃ A e : ℕ,∀ z : Input,
      let W := GeneralPaperCompilerReference.width C d z
      ∀ (_hm : 0<z.m) (hQv : 0<z.Qv) (hp : ∀ j,0<z.weights.read j)
        (b : ℝ) (_hb : 0<b ∧ b<1) (reciprocal : Bool)
        (_hModify : (GeneralPaperProxyClassifier.classify z.m z.k b).choice.modify≠none)
        (_hGuard : ¬(reciprocal=true ∧ (GeneralPaperProxyClassifier.classify z.m z.k b).choice.endpoint=0))
        (_hW : 1≤W) (_hK : binaryWordWidth ((prepare z.m z.k).K+1)≤W) (_hM : binaryWordWidth (z.m+1)≤W)
        (_hIndex : binaryWordWidth ((prepare z.m z.k).S+2)≤W) (_hDim : binaryWordWidth (z.m*((prepare z.m z.k).K-1)+3)≤W)
        (_hBatch : binaryWordWidth (((prepare z.m z.k).S+1)*((prepare z.m z.k).K*(prepare z.m z.k).K)+3)≤W)
        (_hT : binaryWordWidth ((GeneralPaperTrajectoryParameters.prepare (alphabet z.m z.k).lambda z.k).rows+1)≤W)
        (_hScatter : binaryWordWidth ((GeneralPaperTrajectoryParameters.prepare (alphabet z.m z.k).lambda z.k).rows+(GeneralPaperTrajectoryParameters.prepare (alphabet z.m z.k).lambda z.k).rows+1)≤W)
        (_hFinalIndex : binaryWordWidth ((prepare z.m z.k).S+4)≤W),
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
            (A*(z.m+1)^3*2^(4*z.k)*(logSize z)^e) := by
  obtain ⟨A,e,hRate⟩ := GeneralPaperSourceModifiedColumnStorageRates.actual_common_word hg
  refine ⟨A,e,?_⟩
  intro z
  dsimp only
  intro hm hQv hp b hb reciprocal hModify hGuard hW hK hM hIndex hDim hBatch hT hScatter hFinalIndex
  let W := GeneralPaperCompilerReference.width C d z
  let prep := GeneralPaperSourceInitializer.prepared z.k z.Qv hQv z.weights hp z.weight_sum b reciprocal
  let v := GeneralPaperNativeRationalValues.selector z.Qv hQv z.weights hp z.weight_sum
  let f := (GeneralPaperProxyClassifier.classify z.m z.k b).choice.proxy
  let inputs := GeneralPaperSharedBasisInputs.prepare z.k prep v f.num f.den reciprocal
  obtain ⟨state,hr,hBound⟩ := GeneralPaperSourceModifiedColumnStorage.actual_reached hg W z.k z.Qv hm hQv z.weights hp z.weight_sum b hb reciprocal hModify hGuard
    hW hK hM hIndex hDim hBatch hT hScatter hFinalIndex
  refine ⟨state,hr,?_⟩
  exact GeneralPaperSourceModifiedColumnStorage.bound_mono _ _ _ _ (hRate z) hBound

theorem construction_common_word {model : RationalCostModel} {C d : ℕ}
    (hg : GeneralPaperFastRationalModel.Growth model C d) :
    ∃ A e : ℕ,∀ z : Input,
      let W := GeneralPaperCompilerReference.width C d z
      ∀ (_hm : 0<z.m) (hQv : 0<z.Qv) (hp : ∀ j,0<z.weights.read j)
        (b : ℝ) (_hb : 0<b ∧ b<1) (reciprocal : Bool)
        (_hModify : (GeneralPaperProxyClassifier.classify z.m z.k b).choice.modify≠none)
        (_hW : 1≤W) (_hK : binaryWordWidth ((prepare z.m z.k).K+1)≤W) (_hM : binaryWordWidth (z.m+1)≤W)
        (_hIndex : binaryWordWidth ((prepare z.m z.k).S+2)≤W) (_hDim : binaryWordWidth (z.m*((prepare z.m z.k).K-1)+3)≤W)
        (_hBatch : binaryWordWidth (((prepare z.m z.k).S+1)*((prepare z.m z.k).K*(prepare z.m z.k).K)+3)≤W)
        (_hFinalIndex : binaryWordWidth ((prepare z.m z.k).S+4)≤W),
        ∀ outer ho inner hi,GeneralPaperSourceModifiedColumnStorage.window model W z.k z.Qv hQv z.weights hp z.weight_sum b reciprocal outer ho inner hi≤
          A*(z.m+1)^3*2^(4*z.k)*(logSize z)^e := by
  obtain ⟨A,e,hRate⟩ := GeneralPaperSourceModifiedColumnStorageRates.actual_common_word hg
  refine ⟨A,e,?_⟩
  intro z
  dsimp only
  intro hm hQv hp b hb reciprocal hModify hW hK hM hIndex hDim hBatch hFinalIndex outer ho inner hi
  exact (GeneralPaperSourceModifiedColumnStorage.source_construction model (GeneralPaperCompilerReference.width C d z)
    z.k z.Qv hm hQv z.weights hp z.weight_sum b hb reciprocal hModify hW hK hM hIndex hDim hBatch hFinalIndex).1 outer ho inner hi |>.trans
      ((Nat.le_add_left _ _).trans (hRate z))

theorem guard_common_word {model : RationalCostModel} {C d : ℕ}
    (hg : GeneralPaperFastRationalModel.Growth model C d) :
    ∃ A e : ℕ,∀ z : Input,
      let W := GeneralPaperCompilerReference.width C d z
      ∀ (_hm : 0<z.m) (hQv : 0<z.Qv) (hp : ∀ j,0<z.weights.read j)
        (b : ℝ) (_hb : 0<b ∧ b<1) (reciprocal : Bool)
        (_hModify : (GeneralPaperProxyClassifier.classify z.m z.k b).choice.modify≠none)
        (_hGuard : reciprocal=true ∧ (GeneralPaperProxyClassifier.classify z.m z.k b).choice.endpoint=0)
        (_hW : 1≤W) (_hK : binaryWordWidth ((prepare z.m z.k).K+1)≤W) (_hM : binaryWordWidth (z.m+1)≤W)
        (_hIndex : binaryWordWidth ((prepare z.m z.k).S+2)≤W),
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
            A*(z.m+1)^3*2^(4*z.k)*(logSize z)^e := by
  obtain ⟨A,e,hRate⟩ := GeneralPaperSourceModifiedColumnStorageRates.actual_common_word hg
  refine ⟨A,e,?_⟩
  intro z
  dsimp only
  intro hm hQv hp b hb reciprocal hModify hGuard hW hK hM hIndex
  exact (GeneralPaperSourceModifiedColumnStorage.guard_stage model C d (GeneralPaperCompilerReference.width C d z)
    z.k z.Qv hm hQv z.weights hp z.weight_sum b hb reciprocal hModify hGuard hW hK hM hIndex).trans (hRate z)

end Blotto.GeneralPaperSourceModifiedColumnReachedRates
