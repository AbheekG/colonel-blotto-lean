import Blotto.GeneralPaperSourceDictionaryNormalizationStorage

/-! Complete actual native nested anchor normalization, old/returned
physical columns and shared labels SUM with all previous strict/source/
endpoint reserves. Original source heights derive every premise; source
quantization constructors and remaining callers/global joins stay separate. -/
namespace Blotto.GeneralPaperSourceDictionaryNormalizationReachedRates
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
        (_hFinalIndex : binaryWordWidth ((prepare z.m z.k).S+4)≤W),
        let prep := GeneralPaperSourceInitializer.prepared z.k z.Qv hQv z.weights hp z.weight_sum b reciprocal
        let v := GeneralPaperNativeRationalValues.selector z.Qv hQv z.weights hp z.weight_sum
        let f := (GeneralPaperProxyClassifier.classify z.m z.k b).choice.proxy
        let inputs := GeneralPaperSharedBasisInputs.prepare z.k prep v f.num f.den reciprocal
        ∃ state,(GeneralPaperBasisControllerBits.stages model W prep.dictionary.label inputs.matrix (prepare z.m z.k).S prep.threshold
          inputs.controls.N inputs.betaN inputs.initialGrid (z.m*((prepare z.m z.k).K-1)) le_rfl).1=some state ∧
          GeneralPaperSourceDictionaryNormalizationStorage.AtBound model W z.k
            (A*(z.m+1)^3*2^(4*z.k)*(logSize z)^e) b reciprocal prep inputs state
            (GeneralPaperSourceEnclosingOwners.window model W z.k z.Qv hQv z.weights hp z.weight_sum b reciprocal)
            (GeneralPaperSourceStrictConstructorStorage.parentWindow model W z.k z.Qv hQv z.weights hp z.weight_sum b reciprocal)
            (GeneralPaperSourceEnclosingOwners.columns model W z.k z.Qv z.weights b reciprocal)
            (GeneralPaperRetainedFieldValues.run true model W z.Qv hQv z.weights hp z.weight_sum).1
            (GeneralPaperInitializerPreparedPoint.ownBudget z.m z.k b reciprocal) (GeneralPaperInitializerPreparedPoint.opposingBudget z.m z.k b reciprocal)
            (GeneralPaperSourceDictionaryNormalizationStorage.quantized model W z.k z.Qv z.weights b reciprocal) := by
  obtain ⟨A,e,hRate⟩ := GeneralPaperSourceDictionaryNormalizationStorageRates.actual_common_word hg
  refine ⟨A,e,?_⟩
  intro z
  dsimp only
  intro hm hQv hp b hb reciprocal hModify hGuard hW hK hM hIndex hDim hBatch hFinalIndex
  let W := GeneralPaperCompilerReference.width C d z
  let prep := GeneralPaperSourceInitializer.prepared z.k z.Qv hQv z.weights hp z.weight_sum b reciprocal
  let v := GeneralPaperNativeRationalValues.selector z.Qv hQv z.weights hp z.weight_sum
  let f := (GeneralPaperProxyClassifier.classify z.m z.k b).choice.proxy
  let inputs := GeneralPaperSharedBasisInputs.prepare z.k prep v f.num f.den reciprocal
  obtain ⟨state,hr,hBound⟩ := GeneralPaperSourceDictionaryNormalizationStorage.actual_reached model W z.k z.Qv hm hQv z.weights hp z.weight_sum b hb reciprocal hModify hGuard
    hW hK hM hIndex hDim hBatch hFinalIndex
  refine ⟨state,hr,?_⟩
  exact GeneralPaperSourceDictionaryNormalizationStorage.bound_mono model W z.k b reciprocal prep inputs state _ _ _ _ _ _ _ _ _ (hRate z) hBound

theorem normalization_common_word {model : RationalCostModel} {C d : ℕ}
    (hg : GeneralPaperFastRationalModel.Growth model C d) :
    ∃ A e : ℕ,∀ z : Input,
      let W := GeneralPaperCompilerReference.width C d z
      ∀ (b : ℝ) (_hb : 0<b ∧ b<1) (reciprocal : Bool)
        (_hW : 1≤W) (_hK : binaryWordWidth ((prepare z.m z.k).K+1)≤W) (_hM : binaryWordWidth (z.m+1)≤W),
        GeneralPaperSourceDictionaryNormalizationStorage.NormalizationBound model W z.k
          (A*(z.m+1)^3*2^(4*z.k)*(logSize z)^e) (GeneralPaperInitializerPreparedPoint.ownBudget z.m z.k b reciprocal)
          (GeneralPaperSourceDictionaryNormalizationStorage.quantized model W z.k z.Qv z.weights b reciprocal) := by
  obtain ⟨A,e,hRate⟩ := GeneralPaperSourceDictionaryNormalizationStorageRates.actual_common_word hg
  refine ⟨A,e,?_⟩
  intro z
  dsimp only
  intro b hb reciprocal hW hK hM
  let W := GeneralPaperCompilerReference.width C d z
  have h := (GeneralPaperSourceDictionaryNormalizationStorage.source_normalization model W z.k z.Qv z.weights b hb reciprocal hW hK hM).1
  exact GeneralPaperSourceDictionaryNormalizationStorage.normalization_mono model W z.k _ _ _ _
    ((Nat.le_add_left _ _).trans (hRate z)) h

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
          GeneralPaperSourceDictionaryNormalizationStorageRates.sourceProfile model W z.m z.k≤
            A*(z.m+1)^3*2^(4*z.k)*(logSize z)^e := by
  obtain ⟨A,e,hRate⟩ := GeneralPaperSourceDictionaryNormalizationStorageRates.actual_common_word hg
  refine ⟨A,e,?_⟩
  intro z
  dsimp only
  intro hm hQv hp b hb reciprocal hModify hGuard hW hK hM hIndex
  exact (GeneralPaperSourceDictionaryNormalizationStorage.guard_stage model (GeneralPaperCompilerReference.width C d z)
    z.k z.Qv hm hQv z.weights hp z.weight_sum b hb reciprocal hModify hGuard hW hK hM hIndex).trans (hRate z)

end Blotto.GeneralPaperSourceDictionaryNormalizationReachedRates
