import Blotto.GeneralPaperSourceModifiedColumnStorageRates

/-! Actual selected-defender materialization on the retained source
columns, original labels, normalized values and checked native branch.
Complete scalar/inner/outer/caller lifetimes join the previous contract. -/
namespace Blotto.GeneralPaperSourceModifiedColumnStorage
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
  GeneralPaperRetainedModifiedColumnBits.run model W (GeneralPaperScoreScaleParameters.prepare m k).depth (prepare m k).S (prepare m k).H
    (GeneralPaperProxyClassifier.classify m k b).choice.proxy.num (GeneralPaperProxyClassifier.classify m k b).choice.proxy.den
    (GeneralPaperScoreScaleParameters.labels_positive m k) (GeneralPaperSourceEnclosingOwners.columns model W k Qv weights b reciprocal)
    (GeneralPaperRetainedFieldValues.run true model W Qv hQv weights hp hs).1
    (ownBudget m k b reciprocal) (opposingBudget m k b reciprocal) reciprocal
    (GeneralPaperSourceFinalCheckStorage.endpointFraction model W m k b) (GeneralPaperProxyClassifier.classify m k b).choice.endpoint

noncomputable def window {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv)
    (b : ℝ) (reciprocal : Bool) (outer : ℕ) (ho : outer≤m) (inner : ℕ) (hi : inner≤(prepare m k).K) : ℕ :=
  GeneralPaperRetainedModifiedColumnStorage.window model W (GeneralPaperScoreScaleParameters.prepare m k).depth (prepare m k).S (prepare m k).H
    (GeneralPaperProxyClassifier.classify m k b).choice.proxy.num (GeneralPaperProxyClassifier.classify m k b).choice.proxy.den
    (GeneralPaperScoreScaleParameters.labels_positive m k) (GeneralPaperSourceEnclosingOwners.columns model W k Qv weights b reciprocal)
    (GeneralPaperRetainedFieldValues.run true model W Qv hQv weights hp hs).1
    (ownBudget m k b reciprocal) (opposingBudget m k b reciprocal) reciprocal
    (GeneralPaperSourceFinalCheckStorage.endpointFraction model W m k b) (GeneralPaperProxyClassifier.classify m k b).choice.endpoint outer ho inner hi

theorem values_injective {m : ℕ} : Function.Injective (GeneralPaperRetainedFieldValues.selector (m:=m)) := by
  intro a b h
  have hv : a.values=b.values := GeneralPaperNativeQuantizedLabels.table_ext a.values b.values (fun j => congrArg (fun v : RationalFieldSelector m => v.weight j) h)
  cases a
  cases b
  dsimp only at hv
  cases hv
  rfl

theorem physical_inputs {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv)
    (b : ℝ) (reciprocal : Bool)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column (GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows (prepare m k).K))
    (values : GeneralPaperRetainedFieldValues.Values m)
    (hColumns : GeneralPaperRowQuantizer.dictionary columns=GeneralPaperSourceUnchangedDictionary.run k Qv weights b reciprocal)
    (hValues : GeneralPaperRetainedFieldValues.selector values=GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs) :
    columns=GeneralPaperSourceEnclosingOwners.columns model W k Qv weights b reciprocal ∧
      values=(GeneralPaperRetainedFieldValues.run true model W Qv hQv weights hp hs).1 :=
  ⟨GeneralPaperRetainedBitData.dictionary_injective (hColumns.trans (GeneralPaperSourceEnclosingOwners.column_data model W k Qv weights b reciprocal).symm),
    values_injective (hValues.trans (GeneralPaperRetainedFieldValues.selector_data true model W Qv hQv weights hp hs).symm)⟩

theorem native_result {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv)
    (b : ℝ) (reciprocal : Bool) (hm : 0<m) (hb : 0<b ∧ b<1) :
    (run model W k Qv hQv weights hp hs b reciprocal).1.map GeneralPaperRowQuantizer.dictionary=
      GeneralPaperCheckedSourcePair.modified k Qv hQv weights hp hs b reciprocal := by
  let f := (GeneralPaperProxyClassifier.classify m k b).choice.proxy
  let endpoint := GeneralPaperSourceFinalCheckStorage.endpointFraction model W m k b
  let value := (GeneralPaperProxyClassifier.classify m k b).choice.endpoint
  let columns := GeneralPaperSourceEnclosingOwners.columns model W k Qv weights b reciprocal
  let values := (GeneralPaperRetainedFieldValues.run true model W Qv hQv weights hp hs).1
  have hEndpoint : endpoint.value=value := GeneralPaperRetainedEndpointFraction.actual_value model.rat W m k b
  have hf := GeneralPaperProxyClassifier.proxy_integer_representation m k b hb
  have hBit := GeneralPaperRetainedModifiedColumnBits.data model W k f.num f.den columns values (ownBudget m k b reciprocal) (opposingBudget m k b reciprocal) reciprocal endpoint value hEndpoint hm hf.1 f.den_pos
  exact (congrArg (Option.map GeneralPaperRowQuantizer.dictionary) hBit).trans
    (GeneralPaperRetainedModifiedSource.data model k Qv hm hQv weights hp hs b hb reciprocal columns values
      (GeneralPaperSourceEnclosingOwners.column_data model W k Qv weights b reciprocal)
      (GeneralPaperRetainedFieldValues.selector_data true model W Qv hQv weights hp hs) endpoint hEndpoint)

theorem source_construction {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv)
    (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool)
    (hModify : (GeneralPaperProxyClassifier.classify m k b).choice.modify≠none)
    (hW : 1≤W) (hK : binaryWordWidth ((prepare m k).K+1)≤W) (hM : binaryWordWidth (m+1)≤W)
    (hIndex : binaryWordWidth ((prepare m k).S+2)≤W) (hDim : binaryWordWidth (m*((prepare m k).K-1)+3)≤W)
    (hBatch : binaryWordWidth (((prepare m k).S+1)*((prepare m k).K*(prepare m k).K)+3)≤W)
    (hFinal : binaryWordWidth ((prepare m k).S+4)≤W) :
    (∀ outer ho inner hi,window model W k Qv hQv weights hp hs b reciprocal outer ho inner hi≤
      GeneralPaperSourceModifiedColumnStorageRates.sourceProfile model W m k Qv) ∧
      (run model W k Qv hQv weights hp hs b reciprocal).2≤GeneralPaperSourceModifiedColumnStorageRates.price model W m k Qv := by
  let columns := GeneralPaperSourceEnclosingOwners.columns model W k Qv weights b reciprocal
  let values := (GeneralPaperRetainedFieldValues.run true model W Qv hQv weights hp hs).1
  let own := ownBudget m k b reciprocal
  let opposing := opposingBudget m k b reciprocal
  let f := (GeneralPaperProxyClassifier.classify m k b).choice.proxy
  let endpoint := GeneralPaperSourceFinalCheckStorage.endpointFraction model W m k b
  let value := (GeneralPaperProxyClassifier.classify m k b).choice.endpoint
  let R := GeneralPaperSourceUnitCallerStorageRates.operandWidth m k
  let B := GeneralPaperSourceModifiedColumnPointBounds.resultProfile W m k
  let P := GeneralPaperSourceCompilerBranchStorageRates.price model W m k Qv
  have hColumns := GeneralPaperSourceEnclosingOwners.column_data model W k Qv weights b reciprocal
  have hValues := GeneralPaperRetainedFieldValues.selector_data true model W Qv hQv weights hp hs
  have ha (j l) : RationalHeight ((columns.read j).anchors.read l) (GeneralPaperSourceScoreHeights.anchorHeight m k) := by
    change RationalHeight ((GeneralPaperRowQuantizer.dictionary columns).anchor j l) _
    rw [hColumns,GeneralPaperSourceUnchangedDictionary.eq_prepared k Qv hQv weights hp hs b reciprocal]
    exact GeneralPaperSourceScoreHeights.prepared_anchors k Qv hQv weights hp hs b hb reciprocal j l
  have hR (j l) : rationalWordWidth ((columns.read j).anchors.read l)≤R :=
    (rationalWordWidth_of_height (ha j l)).trans (by unfold R GeneralPaperSourceUnitCallerStorageRates.operandWidth;omega)
  have hv (j) : RationalHeight (values.values.read j) (binaryWordWidth Qv) := by
    change RationalHeight ((GeneralPaperRetainedFieldValues.selector values).weight j) _
    rw [hValues]
    exact GeneralPaperSourceScoreHeights.value_height Qv hQv weights hp hs j
  have hB (result : GeneralPaperSourceEndpointBranch.Result (GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows m (prepare m k).K)
      (hr : (GeneralPaperRetainedCompilerBranchBits.run model W (GeneralPaperScoreScaleParameters.prepare m k).depth (prepare m k).S (prepare m k).H f.num f.den
        (GeneralPaperScoreScaleParameters.labels_positive m k) columns values own opposing reciprocal endpoint value).1=some result) :
      GeneralPaperRetainedCompilerBranchStorage.choiceFoot W result.choice≤B :=
    GeneralPaperSourceModifiedColumnPointBounds.choice model W k Qv hm hQv weights hp hs b hb reciprocal hModify hW hK hM hIndex hDim hBatch hFinal result hr
  have hP := (GeneralPaperSourceCompilerBranchStorage.source_branch model W k Qv hm hQv weights hp hs b hb reciprocal hModify hW hK hM hIndex hDim hBatch hFinal).2
  have hGeneric outer ho inner hi := GeneralPaperRetainedModifiedColumnStorage.bounded model W (GeneralPaperScoreScaleParameters.prepare m k).depth (prepare m k).S
    (prepare m k).H f.num f.den R (binaryWordWidth Qv) B P (GeneralPaperScoreScaleParameters.labels_positive m k)
    columns values own opposing reciprocal endpoint value hR hv hB hP hW hK hM outer ho inner hi
  exact ⟨fun outer ho inner hi => (hGeneric outer ho inner hi).1,(hGeneric 0 (Nat.zero_le _) 0 (Nat.zero_le _)).2⟩

def AtBound {m K : ℕ} (old : ℕ → Prop)
    (space : (outer : ℕ) → outer≤m → (inner : ℕ) → inner≤K → ℕ) (limit : ℕ) : Prop :=
  ∃ D F,old D ∧ (∀ outer ho inner hi,space outer ho inner hi≤F) ∧ D+F≤limit

theorem bound_mono {m K : ℕ} (old : ℕ → Prop)
    (space : (outer : ℕ) → outer≤m → (inner : ℕ) → inner≤K → ℕ) (B C : ℕ) (hBC : B≤C) (h : AtBound old space B) :
    AtBound old space C := by
  obtain ⟨D,F,hOld,hSpace,hSum⟩ := h
  exact ⟨D,F,hOld,hSpace,hSum.trans hBC⟩

theorem retained_construction {m K : ℕ} (old : ℕ → Prop) (owners : ℕ)
    (space : (outer : ℕ) → outer≤m → (inner : ℕ) → inner≤K → ℕ) (limit : ℕ)
    (h : AtBound old space limit) (hOwners : ∀ D,old D → owners≤D) :
    ∀ outer ho inner hi,owners+space outer ho inner hi≤limit := by
  obtain ⟨D,F,hOld,hSpace,hSum⟩ := h
  intro outer ho inner hi
  exact (Nat.add_le_add (hOwners D hOld) (hSpace outer ho inner hi)).trans hSum

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
      AtBound (fun constructionBound => GeneralPaperSourceCompilerBranchStorage.AtBound (fun compilerBound => GeneralPaperSourceColumnCallerStorage.AtBound (fun bound => GeneralPaperSourceRowsCallerStorage.AtBound (fun limit => GeneralPaperSourceUnitCallerStorage.AtBound model W k limit b reciprocal prep inputs state
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
        (GeneralPaperSourceCompilerBranchStorage.window model W k Qv hQv weights hp hs b reciprocal) constructionBound)
        (window model W k Qv hQv weights hp hs b reciprocal) (GeneralPaperSourceModifiedColumnStorageRates.reservation model C d W m k Qv) := by
  dsimp only
  intro state inv
  have hOld := GeneralPaperSourceCompilerBranchStorage.source_stage hg W k Qv hm hQv weights hp hs b hb reciprocal hModify hGuard
    hW hK hM hIndex hDim hBatch hT hScatter hFinalIndex state inv
  exact ⟨GeneralPaperSourceCompilerBranchStorageRates.reservation model C d W m k Qv,
    GeneralPaperSourceModifiedColumnStorageRates.sourceProfile model W m k Qv,hOld,
    (source_construction model W k Qv hm hQv weights hp hs b hb reciprocal hModify hW hK hM hIndex hDim hBatch hFinalIndex).1,le_rfl⟩

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
      AtBound (fun constructionBound => GeneralPaperSourceCompilerBranchStorage.AtBound (fun compilerBound => GeneralPaperSourceColumnCallerStorage.AtBound (fun bound => GeneralPaperSourceRowsCallerStorage.AtBound (fun limit => GeneralPaperSourceUnitCallerStorage.AtBound model W k limit b reciprocal prep inputs state
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
        (GeneralPaperSourceCompilerBranchStorage.window model W k Qv hQv weights hp hs b reciprocal) constructionBound)
        (window model W k Qv hQv weights hp hs b reciprocal) (GeneralPaperSourceModifiedColumnStorageRates.reservation model C d W m k Qv) := by
  obtain ⟨state,hr,hOld⟩ := GeneralPaperSourceCompilerBranchStorage.actual_reached hg W k Qv hm hQv weights hp hs b hb reciprocal hModify hGuard
    hW hK hM hIndex hDim hBatch hT hScatter hFinalIndex
  exact ⟨state,hr,GeneralPaperSourceCompilerBranchStorageRates.reservation model C d W m k Qv,
    GeneralPaperSourceModifiedColumnStorageRates.sourceProfile model W m k Qv,hOld,
    (source_construction model W k Qv hm hQv weights hp hs b hb reciprocal hModify hW hK hM hIndex hDim hBatch hFinalIndex).1,le_rfl⟩

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
      GeneralPaperSourceUnitCallerStorageRates.sourceProfile model W m k+GeneralPaperSourceRowsCallerStorageRates.sourceProfile C d W m k Qv+GeneralPaperSourceColumnCallerStorageRates.sourceProfile model C d W m k Qv+GeneralPaperSourceCompilerBranchStorageRates.sourceProfile model W m k Qv+GeneralPaperSourceModifiedColumnStorageRates.sourceProfile model W m k Qv≤
        GeneralPaperSourceModifiedColumnStorageRates.reservation model C d W m k Qv := by
  have hOld := GeneralPaperSourceCompilerBranchStorage.guard_stage model C d W k Qv _hm hQv weights hp hs b hb reciprocal hModify hGuard hW hK hM hIndex
  exact Nat.add_le_add_right hOld _

end Blotto.GeneralPaperSourceModifiedColumnStorage
