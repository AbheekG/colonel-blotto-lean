import Blotto.GeneralPaperSourceCompilerBranchStorageRates

/-! Actual retained compiler branch on the same physical source columns,
stored values and strict preparation. Native child identities derive all
parent ownership and counters, including the early maximum-score return. -/
namespace Blotto.GeneralPaperSourceCompilerBranchStorage
open RationalOrderCell GeneralPaperProxyParameters GeneralPaperBasisStoredProducts
open GeneralPaperBasisState GeneralPaperBasisInvariant GeneralPaperEncodedScalarStorage
open GeneralPaperInitializerPreparedPoint
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 16384

noncomputable def run {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv)
    (b : ℝ) (reciprocal : Bool) :=
  GeneralPaperRetainedCompilerBranchBits.run model W (GeneralPaperScoreScaleParameters.prepare m k).depth (prepare m k).S (prepare m k).H
    (GeneralPaperProxyClassifier.classify m k b).choice.proxy.num (GeneralPaperProxyClassifier.classify m k b).choice.proxy.den
    (GeneralPaperScoreScaleParameters.labels_positive m k) (GeneralPaperSourceEnclosingOwners.columns model W k Qv weights b reciprocal)
    (GeneralPaperRetainedFieldValues.run true model W Qv hQv weights hp hs).1
    (ownBudget m k b reciprocal) (opposingBudget m k b reciprocal) reciprocal
    (GeneralPaperSourceFinalCheckStorage.endpointFraction model W m k b) (GeneralPaperProxyClassifier.classify m k b).choice.endpoint

noncomputable def window {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv)
    (b : ℝ) (reciprocal : Bool) : ℕ :=
  GeneralPaperRetainedCompilerBranchStorage.window model W (GeneralPaperScoreScaleParameters.prepare m k).depth (prepare m k).S (prepare m k).H
    (GeneralPaperProxyClassifier.classify m k b).choice.proxy.num (GeneralPaperProxyClassifier.classify m k b).choice.proxy.den
    (GeneralPaperScoreScaleParameters.labels_positive m k) (GeneralPaperSourceEnclosingOwners.columns model W k Qv weights b reciprocal)
    (GeneralPaperRetainedFieldValues.run true model W Qv hQv weights hp hs).1
    (ownBudget m k b reciprocal) (opposingBudget m k b reciprocal) reciprocal
    (GeneralPaperSourceFinalCheckStorage.endpointFraction model W m k b) (GeneralPaperProxyClassifier.classify m k b).choice.endpoint

theorem native_result {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv)
    (b : ℝ) (reciprocal : Bool) (hm : 0<m) (hb : 0<b ∧ b<1) :
    (run model W k Qv hQv weights hp hs b reciprocal).1=GeneralPaperCheckedEndpointBranch.run k Qv hQv weights hp hs b reciprocal := by
  let f := (GeneralPaperProxyClassifier.classify m k b).choice.proxy
  let endpoint := GeneralPaperSourceFinalCheckStorage.endpointFraction model W m k b
  let value := (GeneralPaperProxyClassifier.classify m k b).choice.endpoint
  let columns := GeneralPaperSourceEnclosingOwners.columns model W k Qv weights b reciprocal
  let values := (GeneralPaperRetainedFieldValues.run true model W Qv hQv weights hp hs).1
  have hEndpoint : endpoint.value=value := GeneralPaperRetainedEndpointFraction.actual_value model.rat W m k b
  have hf := GeneralPaperProxyClassifier.proxy_integer_representation m k b hb
  exact (GeneralPaperRetainedCompilerBranchBits.data model W k f.num f.den columns values _ _ reciprocal endpoint value hEndpoint hm hf.1 f.den_pos).trans
    (GeneralPaperRetainedCompilerSource.data model k Qv hm hQv weights hp hs b hb reciprocal columns values
      (GeneralPaperSourceEnclosingOwners.column_data model W k Qv weights b reciprocal)
      (GeneralPaperRetainedFieldValues.selector_data true model W Qv hQv weights hp hs) endpoint hEndpoint)

theorem native_labels {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv)
    (b : ℝ) (reciprocal : Bool)
    (result : GeneralPaperSourceEndpointBranch.Result (GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows m (prepare m k).K)
    (hr : (run model W k Qv hQv weights hp hs b reciprocal).1=some result) :
    result.labels=(GeneralPaperRowQuantizer.dictionary (GeneralPaperSourceEnclosingOwners.columns model W k Qv weights b reciprocal)).label :=
  (GeneralPaperRetainedCompilerBranchBits.labels model W (GeneralPaperScoreScaleParameters.prepare m k).depth (prepare m k).S (prepare m k).H
    (GeneralPaperProxyClassifier.classify m k b).choice.proxy.num (GeneralPaperProxyClassifier.classify m k b).choice.proxy.den
    (GeneralPaperScoreScaleParameters.labels_positive m k) (GeneralPaperSourceEnclosingOwners.columns model W k Qv weights b reciprocal)
    (GeneralPaperRetainedFieldValues.run true model W Qv hQv weights hp hs).1
    (ownBudget m k b reciprocal) (opposingBudget m k b reciprocal) reciprocal
    (GeneralPaperSourceFinalCheckStorage.endpointFraction model W m k b) (GeneralPaperProxyClassifier.classify m k b).choice.endpoint result hr).symm

theorem source_branch {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv)
    (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool)
    (hModify : (GeneralPaperProxyClassifier.classify m k b).choice.modify≠none)
    (hW : 1≤W) (hK : binaryWordWidth ((prepare m k).K+1)≤W) (hM : binaryWordWidth (m+1)≤W)
    (hIndex : binaryWordWidth ((prepare m k).S+2)≤W) (hDim : binaryWordWidth (m*((prepare m k).K-1)+3)≤W)
    (hBatch : binaryWordWidth (((prepare m k).S+1)*((prepare m k).K*(prepare m k).K)+3)≤W)
    (hFinal : binaryWordWidth ((prepare m k).S+4)≤W) :
    window model W k Qv hQv weights hp hs b reciprocal≤GeneralPaperSourceCompilerBranchStorageRates.sourceProfile model W m k Qv ∧
      (run model W k Qv hQv weights hp hs b reciprocal).2≤GeneralPaperSourceCompilerBranchStorageRates.price model W m k Qv := by
  let f := (GeneralPaperProxyClassifier.classify m k b).choice.proxy
  let endpoint := GeneralPaperSourceFinalCheckStorage.endpointFraction model W m k b
  let value := (GeneralPaperProxyClassifier.classify m k b).choice.endpoint
  let columns := GeneralPaperSourceEnclosingOwners.columns model W k Qv weights b reciprocal
  let values := (GeneralPaperRetainedFieldValues.run true model W Qv hQv weights hp hs).1
  let own := ownBudget m k b reciprocal
  let opposing := opposingBudget m k b reciprocal
  let retained := GeneralPaperRetainedTransferPreparation.run true model W (GeneralPaperScoreScaleParameters.prepare m k).depth (prepare m k).S
    (GeneralPaperScoreScaleParameters.labels_positive m k) columns values own opposing
  let prep := GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b reciprocal
  let v := GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs
  let inputs := GeneralPaperSharedBasisInputs.prepare k prep v f.num f.den reciprocal
  let raw := GeneralPaperRetainedBasisEndpointBits.run model W (prepare m k).H f.num f.den reciprocal prep inputs.matrix endpoint value
  let reached := GeneralPaperRetainedCompilerBranchStorage.child model W (prepare m k).H f.num f.den reciprocal endpoint value retained
  let R := GeneralPaperSourceUnitCallerStorageRates.operandWidth m k
  let Gamma := GeneralPaperSourceEndpointScalarStorageRates.operandWidth m k
  let Point := GeneralPaperSourceOuterEndpointStorageRates.sourceProfile model W m k
  have hColumns := GeneralPaperSourceEnclosingOwners.column_data model W k Qv weights b reciprocal
  have hValues := GeneralPaperRetainedFieldValues.selector_data true model W Qv hQv weights hp hs
  have hData := GeneralPaperSourceEnclosingOwners.prepared_data model W k Qv hQv weights hp hs b reciprocal
  change retained.1.prepared=prep ∧ retained.1.matrix=inputs.matrix at hData
  have hValue := GeneralPaperEndpointRatioSize.height m k b hb hModify
  change RationalHeight value (binaryWordWidth (prepare m k).qbar) at hValue
  have hGamma : rationalWordWidth (if reciprocal then 1/value else value)≤Gamma := by
    have hOne : RationalHeight (1:ℚ) 1 := by norm_num [RationalHeight]
    cases reciprocal with
    | false => exact (rationalWordWidth_of_height hValue).trans (by unfold Gamma GeneralPaperSourceEndpointScalarStorageRates.operandWidth GeneralPaperRetainedEndpointBitBounds.priceWidth;omega)
    | true => exact (rationalWordWidth_of_height (hOne.div hValue)).trans (by unfold Gamma GeneralPaperSourceEndpointScalarStorageRates.operandWidth GeneralPaperRetainedEndpointBitBounds.priceWidth;omega)
  have hOuter : GeneralPaperSourceOuterEndpointStorage.window model W k b reciprocal prep inputs≤Point ∧
      raw.2≤GeneralPaperSourceOuterEndpointStorageRates.price model W m k := by
    by_cases hGuard : reciprocal=true ∧ value=0
    · have h := GeneralPaperSourceOuterEndpointStorage.source_guard model W k Qv hm hQv weights hp hs b hb reciprocal hModify hGuard
      refine ⟨h.1,?_⟩
      change (GeneralPaperRetainedBasisEndpointBits.run model W (prepare m k).H f.num f.den reciprocal prep inputs.matrix endpoint value).2≤_
      rw [h.2]
      have hPrice := GeneralPaperRetainedEndpointBitBounds.guard_price model W (prepare m k).qbar value hValue
      dsimp only
      exact hPrice.trans (by unfold GeneralPaperSourceOuterEndpointStorageRates.price;omega)
    · exact GeneralPaperSourceOuterEndpointStorage.source_outer model W k Qv hm hQv weights hp hs b hb reciprocal hModify hGuard
        hW hK hM hIndex hDim hBatch hFinal
  have hRawPoint : GeneralPaperRawEndpointReturnStorage.optionFoot W raw.1≤Point := by
    have hOwner : GeneralPaperRawEndpointReturnStorage.optionFoot W raw.1≤GeneralPaperSourceOuterEndpointStorage.window model W k b reciprocal prep inputs := by
      unfold GeneralPaperSourceOuterEndpointStorage.window GeneralPaperOuterEndpointFrameStorage.window
      dsimp only [raw,f,endpoint,value]
      omega
    exact hOwner.trans hOuter.1
  have hOnePoint : 1≤Point := by
    have h : 1≤GeneralPaperRawEndpointReturnStorage.optionFoot W raw.1 := by
      cases raw.1 <;> simp only [GeneralPaperRawEndpointReturnStorage.optionFoot] <;> omega
    exact h.trans hRawPoint
  have hE : reached.2≤GeneralPaperSourceOuterEndpointStorageRates.price model W m k := by
    unfold reached GeneralPaperRetainedCompilerBranchStorage.child
    split
    · exact Nat.zero_le _
    · rw [hData.1,hData.2]
      exact hOuter.2
  have hPoint : GeneralPaperRawEndpointReturnStorage.optionFoot W reached.1≤Point := by
    unfold reached GeneralPaperRetainedCompilerBranchStorage.child
    split
    · exact hOnePoint
    · rw [hData.1,hData.2]
      exact hRawPoint
  have hBounds := GeneralPaperRetainedEndpointBitBounds.fraction_bounds model.rat W m k b hb hModify
  have hFraction := GeneralPaperRetainedEndpointBitBounds.endpoint_price model W (prepare m k).qbar endpoint value hBounds.1 hBounds.2 hValue reciprocal
  have hTag : GeneralPaperRetainedCompilerBranchBits.tagPrice model W reciprocal value≤GeneralPaperSourceCompilerBranchStorageRates.tagPrice model W m k := by
    have h : GeneralPaperRetainedCompilerBranchBits.tagPrice model W reciprocal value≤GeneralPaperRetainedBasisEndpointBits.endpointPrice model W endpoint value reciprocal := by
      unfold GeneralPaperRetainedCompilerBranchBits.tagPrice GeneralPaperRetainedBasisEndpointBits.endpointPrice
      omega
    exact h.trans hFraction
  have hP := GeneralPaperSourceStrictPreparationBits.actual_work model W k Qv hQv weights hp hs b hb reciprocal columns values hColumns hValues hW hK hM hIndex
  have hX := GeneralPaperSourceStrictPreparationBits.threshold_price model W (GeneralPaperScoreScaleParameters.prepare m k).depth (prepare m k).S
    (GeneralPaperScoreScaleParameters.labels_positive m k) columns values own opposing (GeneralPaperScoreScaleParameters.score_cap m k)
  have hThreshold := GeneralPaperSourceStrictPreparationBits.threshold_bound model W (GeneralPaperScoreScaleParameters.prepare m k).depth (prepare m k).S
    (GeneralPaperScoreScaleParameters.labels_positive m k) columns values own opposing
  have hMaximum := GeneralPaperSourceStrictPreparationBits.maximum_bound model W (GeneralPaperScoreScaleParameters.prepare m k).depth (prepare m k).S
    (GeneralPaperScoreScaleParameters.labels_positive m k) columns values own opposing (GeneralPaperScoreScaleParameters.score_cap m k)
  have hf := GeneralPaperProxyClassifier.proxy_integer_representation m k b hb
  have ha (j l) : RationalHeight ((columns.read j).anchors.read l) (GeneralPaperSourceScoreHeights.anchorHeight m k) := by
    change RationalHeight ((GeneralPaperRowQuantizer.dictionary columns).anchor j l) _
    rw [hColumns,GeneralPaperSourceUnchangedDictionary.eq_prepared k Qv hQv weights hp hs b reciprocal]
    exact GeneralPaperSourceScoreHeights.prepared_anchors k Qv hQv weights hp hs b hb reciprocal j l
  have hCol := GeneralPaperEnclosingSourceOwners.columns_bound W R columns (fun j l =>
    (rationalWordWidth_of_height (ha j l)).trans (by unfold R GeneralPaperSourceUnitCallerStorageRates.operandWidth;omega))
  have hv (j) : RationalHeight (values.values.read j) (binaryWordWidth Qv) := by
    change RationalHeight ((GeneralPaperRetainedFieldValues.selector values).weight j) _
    rw [hValues]
    exact GeneralPaperSourceScoreHeights.value_height Qv hQv weights hp hs j
  have ho : rationalWordWidth own≤R := (rationalWordWidth_of_height (GeneralPaperSourceScoreHeights.own_height m k b hb reciprocal)).trans
    (by unfold R GeneralPaperSourceUnitCallerStorageRates.operandWidth GeneralPaperSourceScoreHeights.anchorHeight;omega)
  have hr : rationalWordWidth opposing≤R := (rationalWordWidth_of_height (GeneralPaperSourceStrictPreparationBits.opposing_height m k b hb reciprocal)).trans
    (by unfold R GeneralPaperSourceUnitCallerStorageRates.operandWidth GeneralPaperSourceScoreHeights.anchorHeight;omega)
  exact GeneralPaperRetainedCompilerBranchStorage.bounded model W (GeneralPaperScoreScaleParameters.prepare m k).depth (prepare m k).S
    (prepare m k).H f.num f.den (prepare m k).qbar R (binaryWordWidth Qv) Point Gamma _ _ _ _
    (GeneralPaperScoreScaleParameters.labels_positive m k) columns values own opposing reciprocal endpoint value
    hCol hv ho hr (hf.2.1.le.trans hf.2.2) hf.2.2 hThreshold hMaximum hP hX hE hTag hPoint hGamma

def AtBound (old : ℕ → Prop) (branch limit : ℕ) : Prop := GeneralPaperSourceColumnCallerStorage.AtBound old branch limit

theorem bound_mono (old : ℕ → Prop) (branch B C : ℕ) (hBC : B≤C) (h : AtBound old branch B) :
    AtBound old branch C := GeneralPaperSourceColumnCallerStorage.bound_mono old branch B C hBC h

theorem retained_branch (old : ℕ → Prop) (owners branch limit : ℕ) (h : AtBound old branch limit)
    (hOwners : ∀ D,old D → owners≤D) : owners+branch≤limit :=
  GeneralPaperSourceColumnCallerStorage.retained_columns old owners branch limit h hOwners

theorem source_stage {m : ℕ} {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d) (W k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv)
    (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool)
    (hModify : (GeneralPaperProxyClassifier.classify m k b).choice.modify≠none)
    (hGuard : ¬(reciprocal=true ∧ (GeneralPaperProxyClassifier.classify m k b).choice.endpoint=0))
    (hW : 1≤W) (hK : binaryWordWidth ((prepare m k).K+1)≤W) (hM : binaryWordWidth (m+1)≤W)
    (hIndex : binaryWordWidth ((prepare m k).S+2)≤W) (hDim : binaryWordWidth (m*((prepare m k).K-1)+3)≤W)
    (hBatch : binaryWordWidth (((prepare m k).S+1)*((prepare m k).K*(prepare m k).K)+3)≤W)
    (hT : binaryWordWidth ((GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows+1)≤W)
    (hScatter : binaryWordWidth ((GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows+(GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows+1)≤W)
    (hFinalIndex : binaryWordWidth ((prepare m k).S+4)≤W) :
    let prep := GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b reciprocal
    let v := GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs
    let f := (GeneralPaperProxyClassifier.classify m k b).choice.proxy
    let inputs := GeneralPaperSharedBasisInputs.prepare k prep v f.num f.den reciprocal
    ∀ state,Invariant prep.dictionary v (prepare m k).S prep.threshold inputs.controls.N inputs.betaN inputs.initialGrid le_rfl state →
      AtBound (fun compilerBound => GeneralPaperSourceColumnCallerStorage.AtBound (fun bound => GeneralPaperSourceRowsCallerStorage.AtBound (fun limit => GeneralPaperSourceUnitCallerStorage.AtBound model W k limit b reciprocal prep inputs state
        (GeneralPaperSourceEnclosingOwners.window model W k Qv hQv weights hp hs b reciprocal)
        (GeneralPaperSourceStrictConstructorStorage.parentWindow model W k Qv hQv weights hp hs b reciprocal)
        (GeneralPaperSourceEnclosingOwners.columns model W k Qv weights b reciprocal)
        (GeneralPaperRetainedFieldValues.run true model W Qv hQv weights hp hs).1
        (GeneralPaperInitializerPreparedPoint.ownBudget m k b reciprocal) (GeneralPaperInitializerPreparedPoint.opposingBudget m k b reciprocal)
        (GeneralPaperSourceDictionaryNormalizationStorage.quantized model W k Qv weights b reciprocal)
        (GeneralPaperSourceQuantizedAnchorStorage.window model W k Qv weights b reciprocal)
        (GeneralPaperSourceRepresentativeSortStorage.window model W k Qv weights b reciprocal)
        (GeneralPaperSourceColumnInputStorage.window model W k Qv weights b reciprocal)
        (GeneralPaperSourceBlockDivisionStorage.window model W m k)
        (GeneralPaperSourceLabelScatterStorage.window model W k Qv weights b reciprocal)
        (GeneralPaperSourceQuantizationParentStorage.window model W k Qv weights b reciprocal)
        (GeneralPaperSourceUnitCallerStorage.window model W k Qv weights b reciprocal))
        (GeneralPaperSourceRowsCallerStorage.window model W k Qv weights b reciprocal) bound)
        (GeneralPaperSourceColumnCallerStorage.window model W k Qv weights b reciprocal) compilerBound)
        (window model W k Qv hQv weights hp hs b reciprocal) (GeneralPaperSourceCompilerBranchStorageRates.reservation model C d W m k Qv) := by
  dsimp only
  intro state inv
  have hOld := GeneralPaperSourceColumnCallerStorage.source_stage hg W k Qv hm hQv weights hp hs b hb reciprocal hModify hGuard
    hW hK hM hIndex hDim hBatch hT hScatter hFinalIndex state inv
  exact ⟨GeneralPaperSourceColumnCallerStorageRates.reservation model C d W m k Qv,
    GeneralPaperSourceCompilerBranchStorageRates.sourceProfile model W m k Qv,hOld,
    (source_branch model W k Qv hm hQv weights hp hs b hb reciprocal hModify hW hK hM hIndex hDim hBatch hFinalIndex).1,le_rfl⟩

theorem actual_reached {m : ℕ} {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d) (W k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv)
    (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool)
    (hModify : (GeneralPaperProxyClassifier.classify m k b).choice.modify≠none)
    (hGuard : ¬(reciprocal=true ∧ (GeneralPaperProxyClassifier.classify m k b).choice.endpoint=0))
    (hW : 1≤W) (hK : binaryWordWidth ((prepare m k).K+1)≤W) (hM : binaryWordWidth (m+1)≤W)
    (hIndex : binaryWordWidth ((prepare m k).S+2)≤W) (hDim : binaryWordWidth (m*((prepare m k).K-1)+3)≤W)
    (hBatch : binaryWordWidth (((prepare m k).S+1)*((prepare m k).K*(prepare m k).K)+3)≤W)
    (hT : binaryWordWidth ((GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows+1)≤W)
    (hScatter : binaryWordWidth ((GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows+(GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows+1)≤W)
    (hFinalIndex : binaryWordWidth ((prepare m k).S+4)≤W) :
    let prep := GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b reciprocal
    let v := GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs
    let f := (GeneralPaperProxyClassifier.classify m k b).choice.proxy
    let inputs := GeneralPaperSharedBasisInputs.prepare k prep v f.num f.den reciprocal
    ∃ state,(GeneralPaperBasisControllerBits.stages model W prep.dictionary.label inputs.matrix (prepare m k).S prep.threshold
      inputs.controls.N inputs.betaN inputs.initialGrid (m*((prepare m k).K-1)) le_rfl).1=some state ∧
      AtBound (fun compilerBound => GeneralPaperSourceColumnCallerStorage.AtBound (fun bound => GeneralPaperSourceRowsCallerStorage.AtBound (fun limit => GeneralPaperSourceUnitCallerStorage.AtBound model W k limit b reciprocal prep inputs state
        (GeneralPaperSourceEnclosingOwners.window model W k Qv hQv weights hp hs b reciprocal)
        (GeneralPaperSourceStrictConstructorStorage.parentWindow model W k Qv hQv weights hp hs b reciprocal)
        (GeneralPaperSourceEnclosingOwners.columns model W k Qv weights b reciprocal)
        (GeneralPaperRetainedFieldValues.run true model W Qv hQv weights hp hs).1
        (GeneralPaperInitializerPreparedPoint.ownBudget m k b reciprocal) (GeneralPaperInitializerPreparedPoint.opposingBudget m k b reciprocal)
        (GeneralPaperSourceDictionaryNormalizationStorage.quantized model W k Qv weights b reciprocal)
        (GeneralPaperSourceQuantizedAnchorStorage.window model W k Qv weights b reciprocal)
        (GeneralPaperSourceRepresentativeSortStorage.window model W k Qv weights b reciprocal)
        (GeneralPaperSourceColumnInputStorage.window model W k Qv weights b reciprocal)
        (GeneralPaperSourceBlockDivisionStorage.window model W m k)
        (GeneralPaperSourceLabelScatterStorage.window model W k Qv weights b reciprocal)
        (GeneralPaperSourceQuantizationParentStorage.window model W k Qv weights b reciprocal)
        (GeneralPaperSourceUnitCallerStorage.window model W k Qv weights b reciprocal))
        (GeneralPaperSourceRowsCallerStorage.window model W k Qv weights b reciprocal) bound)
        (GeneralPaperSourceColumnCallerStorage.window model W k Qv weights b reciprocal) compilerBound)
        (window model W k Qv hQv weights hp hs b reciprocal) (GeneralPaperSourceCompilerBranchStorageRates.reservation model C d W m k Qv) := by
  obtain ⟨state,hr,hOld⟩ := GeneralPaperSourceColumnCallerStorage.actual_reached hg W k Qv hm hQv weights hp hs b hb reciprocal hModify hGuard
    hW hK hM hIndex hDim hBatch hT hScatter hFinalIndex
  exact ⟨state,hr,GeneralPaperSourceColumnCallerStorageRates.reservation model C d W m k Qv,
    GeneralPaperSourceCompilerBranchStorageRates.sourceProfile model W m k Qv,hOld,
    (source_branch model W k Qv hm hQv weights hp hs b hb reciprocal hModify hW hK hM hIndex hDim hBatch hFinalIndex).1,le_rfl⟩

theorem guard_stage {m : ℕ} (model : RationalCostModel) (C d W k Qv : ℕ) (_hm : 0<m) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv)
    (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool)
    (hModify : (GeneralPaperProxyClassifier.classify m k b).choice.modify≠none)
    (hGuard : reciprocal=true ∧ (GeneralPaperProxyClassifier.classify m k b).choice.endpoint=0)
    (hW : 1≤W) (hK : binaryWordWidth ((prepare m k).K+1)≤W) (hM : binaryWordWidth (m+1)≤W)
    (hIndex : binaryWordWidth ((prepare m k).S+2)≤W) :
    let prep := GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b reciprocal
    let v := GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs
    let f := (GeneralPaperProxyClassifier.classify m k b).choice.proxy
    let inputs := GeneralPaperSharedBasisInputs.prepare k prep v f.num f.den reciprocal
    GeneralPaperSourceOuterEndpointStorage.window model W k b reciprocal prep inputs+
      GeneralPaperSourceEndpointFractionConstructionStorage.window model W m k b+
      GeneralPaperSourceEnclosingOwners.window model W k Qv hQv weights hp hs b reciprocal+
      GeneralPaperSourceStrictConstructorStorage.parentWindow model W k Qv hQv weights hp hs b reciprocal+
      GeneralPaperSourceMatrixStorage.sourceProfile model W m k Qv+GeneralPaperSourceScoreStorage.profile model W m k+
      GeneralPaperScoreResidencyRates.initialProfile model W m k+GeneralPaperSourceScoreResidents.thresholdProfile model W m k+
      GeneralPaperSourceGuardStorage.sourceProfile model W m k Qv+
      GeneralPaperSourceDictionaryNormalizationStorageRates.sourceProfile model W m k+
      GeneralPaperSourceQuantizedAnchorStorageRates.sourceProfile model W m k+
      GeneralPaperSourceRepresentativeSortStorageRates.sourceProfile model W m k+
      GeneralPaperSourceColumnInputStorageRates.sourceProfile model W m k+
      GeneralPaperSourceBlockDivisionStorageRates.sourceProfile model W m k+
      GeneralPaperSourceLabelScatterStorageRates.sourceProfile model W m k+
      GeneralPaperSourceQuantizationParentStorageRates.sourceProfile model W m k+
      GeneralPaperSourceUnitCallerStorageRates.sourceProfile model W m k+GeneralPaperSourceRowsCallerStorageRates.sourceProfile C d W m k Qv+GeneralPaperSourceColumnCallerStorageRates.sourceProfile model C d W m k Qv+GeneralPaperSourceCompilerBranchStorageRates.sourceProfile model W m k Qv≤
        GeneralPaperSourceCompilerBranchStorageRates.reservation model C d W m k Qv := by
  have hOld := GeneralPaperSourceColumnCallerStorage.guard_stage model C d W k Qv _hm hQv weights hp hs b hb reciprocal hModify hGuard hW hK hM hIndex
  exact Nat.add_le_add_right hOld _

end Blotto.GeneralPaperSourceCompilerBranchStorage
