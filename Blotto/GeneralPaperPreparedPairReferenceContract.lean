import Blotto.GeneralPaperPreparedPairReference

/-! The derived full-lifetime reference applies to actual native prepared
arrays, genuine work, arbitrary addresses in every completed reserve and
prior native controller/guard contracts. No local word/capacity or final
state oracle is supplied. Remaining outer driver phases stay separate. -/
namespace Blotto.GeneralPaperPreparedPairReferenceContract
open GeneralPaperSourceWordGrowth GeneralPaperProxyParameters
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 7000000
set_option maxRecDepth 16384

theorem modified_reserve_le (model : RationalCostModel) (C d W m k Qv B : ℕ) :
    GeneralPaperSourceModifiedColumnStorageRates.reservation model C d W m k Qv≤
      GeneralPaperSourcePreparedPairOwnerRates.reservation model C d W m k Qv B := by
  unfold GeneralPaperSourcePreparedPairOwnerRates.reservation GeneralPaperSourceCompilerPairStorageRates.reservation
  omega

theorem complete_reserve_capacity {model : RationalCostModel} {C d : ℕ}
    (hg : GeneralPaperFastRationalModel.Growth model C d) (x : Input) :
    let W := GeneralPaperPreparedPairReference.width C d x
    GeneralPaperSourcePreparedPairOwnerRates.reservation model C d W x.m x.k x.Qv x.B<2^W :=
  (GeneralPaperPreparedPairReference.actual_reserve hg _ x).trans_lt (GeneralPaperPreparedPairReference.capacity C d x)

theorem reserved_address {model : RationalCostModel} {C d : ℕ}
    (hg : GeneralPaperFastRationalModel.Growth model C d) (x : Input) (address : ℕ)
    (h : address≤GeneralPaperSourcePreparedPairOwnerRates.reservation model C d
      (GeneralPaperPreparedPairReference.width C d x) x.m x.k x.Qv x.B) :
    binaryWordWidth address≤GeneralPaperPreparedPairReference.width C d x :=
  GeneralPaperPreparedPairReference.address_word C d x address (h.trans (GeneralPaperPreparedPairReference.actual_reserve hg _ x))

theorem row_words (C d : ℕ) (x : Input) :
    let W := GeneralPaperPreparedPairReference.width C d x
    binaryWordWidth ((GeneralPaperTrajectoryParameters.prepare (alphabet x.m x.k).lambda x.k).rows+1)≤W ∧
    binaryWordWidth ((GeneralPaperTrajectoryParameters.prepare (alphabet x.m x.k).lambda x.k).rows+
      (GeneralPaperTrajectoryParameters.prepare (alphabet x.m x.k).lambda x.k).rows+1)≤W := by
  have h := (GeneralPaperPreparedPairReference.local_words C d x).2.2.2.2.2.2.2
  refine ⟨?_,?_⟩
  · exact (binaryWordWidth_mono (show
      (GeneralPaperTrajectoryParameters.prepare (alphabet x.m x.k).lambda x.k).rows+1≤
      2*(GeneralPaperTrajectoryParameters.prepare (alphabet x.m x.k).lambda x.k).rows+(prepare x.m x.k).K+x.m+1 by omega)).trans h
  · exact (binaryWordWidth_mono (show
      (GeneralPaperTrajectoryParameters.prepare (alphabet x.m x.k).lambda x.k).rows+
        (GeneralPaperTrajectoryParameters.prepare (alphabet x.m x.k).lambda x.k).rows+1≤
      2*(GeneralPaperTrajectoryParameters.prepare (alphabet x.m x.k).lambda x.k).rows+(prepare x.m x.k).K+x.m+1 by omega)).trans h

theorem native_window {model : RationalCostModel} {C d : ℕ}
    (hg : GeneralPaperFastRationalModel.Growth model C d) (x : Input) (hm : 0<x.m) (hQv : 0<x.Qv)
    (hp : ∀ j,0<x.weights.read j) :
    let W := GeneralPaperPreparedPairReference.width C d x
    ∀ cursor hc outer ho inner hi,
      GeneralPaperSourcePreparedPairOwners.window model W x.k x.Qv hQv x.weights hp x.weight_sum x.b cursor hc outer ho inner hi≤
        GeneralPaperPreparedPairReference.profile C d W x ∧
      (GeneralPaperSourcePreparedPairOwners.run model W x.k x.Qv hQv x.weights hp x.weight_sum x.b).2≤
        GeneralPaperSourcePreparedPairOwners.price model C d W x.m x.k x.Qv ∧
      (∀ address,address≤GeneralPaperSourcePreparedPairOwners.window model W x.k x.Qv hQv x.weights hp x.weight_sum x.b cursor hc outer ho inner hi →
        binaryWordWidth address≤W) := by
  dsimp only
  intro cursor hc outer ho inner hi
  have hw := GeneralPaperPreparedPairReference.positive_width C d x
  have h := GeneralPaperPreparedPairReference.local_words C d x
  have hr := row_words C d x
  have hNative := GeneralPaperSourcePreparedPairOwners.bounded model (GeneralPaperPreparedPairReference.width C d x)
    x.k x.Qv hQv x.weights hp x.weight_sum x.b C d x.B hg hm x.hb x.hB hw h.2.1 h.2.2.1 h.2.2.2.1 h.1 h.2.2.2.2.1 h.2.2.2.2.2.1 hr.2
    cursor hc outer ho inner hi
  have hWindow := hNative.1.trans ((Nat.le_add_left _ _).trans (GeneralPaperPreparedPairReference.actual_reserve hg _ x))
  exact ⟨hWindow,hNative.2,fun address hAddress => GeneralPaperPreparedPairReference.address_word C d x address (hAddress.trans hWindow)⟩

theorem paper_space {model : RationalCostModel} {C d : ℕ}
    (hg : GeneralPaperFastRationalModel.Growth model C d) :
    ∃ A e : ℕ,∀ (x : Input) (_hm : 0<x.m) (hQv : 0<x.Qv) (hp : ∀ j,0<x.weights.read j),
      let W := GeneralPaperPreparedPairReference.width C d x
      ∀ cursor hc outer ho inner hi,
        GeneralPaperSourcePreparedPairOwners.window model W x.k x.Qv hQv x.weights hp x.weight_sum x.b cursor hc outer ho inner hi≤
          A*(x.B+1+(x.m+1)^3*2^(4*x.k))*(logSize x)^e := by
  obtain ⟨A,e,h⟩ := GeneralPaperPreparedPairReference.common_word_bound C d
  exact ⟨A,e,fun x hm hQv hp cursor hc outer ho inner hi =>
    ((native_window hg x hm hQv hp cursor hc outer ho inner hi).1).trans (h x)⟩

theorem reached_controller {model : RationalCostModel} {C d : ℕ}
    (hg : GeneralPaperFastRationalModel.Growth model C d) :
    ∀ z : Input,
      let W := GeneralPaperPreparedPairReference.width C d z
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
            (GeneralPaperPreparedPairReference.profile C d W z) := by
  intro z
  dsimp only
  intro hm hQv hp b hb reciprocal hModify hGuard
  let W := GeneralPaperPreparedPairReference.width C d z
  have hw := GeneralPaperPreparedPairReference.positive_width C d z
  have h := GeneralPaperPreparedPairReference.local_words C d z
  have hr := row_words C d z
  have hTop := (modified_reserve_le model C d W z.m z.k z.Qv z.B).trans
    (GeneralPaperPreparedPairReference.actual_reserve hg W z)
  obtain ⟨state,hNative,hBound⟩ := GeneralPaperSourceModifiedColumnStorage.actual_reached hg W z.k z.Qv hm hQv z.weights hp z.weight_sum b hb reciprocal hModify hGuard
    hw h.2.1 h.2.2.1 h.2.2.2.1 h.1 h.2.2.2.2.1 hr.1 hr.2 h.2.2.2.2.2.1
  refine ⟨state,hNative,?_⟩
  exact GeneralPaperSourceModifiedColumnStorage.bound_mono _ _ _ _ hTop hBound

theorem guard_lifetimes {model : RationalCostModel} {C d : ℕ}
    (hg : GeneralPaperFastRationalModel.Growth model C d) :
    ∀ z : Input,
      let W := GeneralPaperPreparedPairReference.width C d z
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
            GeneralPaperPreparedPairReference.profile C d W z := by
  intro z
  dsimp only
  intro hm hQv hp b hb reciprocal hModify hGuard
  let W := GeneralPaperPreparedPairReference.width C d z
  have hw := GeneralPaperPreparedPairReference.positive_width C d z
  have h := GeneralPaperPreparedPairReference.local_words C d z
  have hr := row_words C d z
  have hTop := (modified_reserve_le model C d W z.m z.k z.Qv z.B).trans
    (GeneralPaperPreparedPairReference.actual_reserve hg W z)
  exact (GeneralPaperSourceModifiedColumnStorage.guard_stage model C d W z.k z.Qv hm hQv z.weights hp z.weight_sum b hb reciprocal hModify hGuard
    hw h.2.1 h.2.2.1 h.2.2.2.1).trans hTop

theorem simultaneous_window {model : RationalCostModel} {C d : ℕ}
    (hg : GeneralPaperFastRationalModel.Growth model C d) (x : Input) (hm : 0<x.m) (hQv : 0<x.Qv)
    (hp : ∀ j,0<x.weights.read j) (oldOwner : ℕ)
    (hOld : oldOwner≤GeneralPaperSourceCompilerPairStorageRates.reservation model C d
      (GeneralPaperPreparedPairReference.width C d x) x.m x.k x.Qv) :
    let W := GeneralPaperPreparedPairReference.width C d x
    ∀ cursor hc outer ho inner hi,
      oldOwner+GeneralPaperSourcePreparedPairOwners.window model W x.k x.Qv hQv x.weights hp x.weight_sum x.b cursor hc outer ho inner hi≤
        GeneralPaperPreparedPairReference.profile C d W x := by
  dsimp only
  intro cursor hc outer ho inner hi
  have hw := GeneralPaperPreparedPairReference.positive_width C d x
  have h := GeneralPaperPreparedPairReference.local_words C d x
  have hr := row_words C d x
  have hNative := (GeneralPaperSourcePreparedPairOwners.bounded model (GeneralPaperPreparedPairReference.width C d x)
    x.k x.Qv hQv x.weights hp x.weight_sum x.b C d x.B hg hm x.hb x.hB hw h.2.1 h.2.2.1 h.2.2.2.1 h.1 h.2.2.2.2.1 h.2.2.2.2.2.1 hr.2
    cursor hc outer ho inner hi).1
  exact (Nat.add_le_add hOld hNative).trans (GeneralPaperPreparedPairReference.actual_reserve hg _ x)

end Blotto.GeneralPaperPreparedPairReferenceContract
