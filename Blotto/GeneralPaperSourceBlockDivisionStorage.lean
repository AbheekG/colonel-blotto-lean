import Blotto.GeneralPaperSourceBlockDivisionStorageRates
import Blotto.GeneralPaperRetainedSourceColumnBits

/-! Actual one-time native block-size division and every occurrence-
label division. Operand/depth facts follow from the genuine native block
and original row count. Their erased stack windows SUM with all prior
materialization/sort/anchor/source/strict/endpoint ownership contracts. -/
namespace Blotto.GeneralPaperSourceBlockDivisionStorage
open RationalOrderCell GeneralPaperProxyParameters GeneralPaperBasisStoredProducts
open GeneralPaperBasisState GeneralPaperBasisInvariant GeneralPaperEncodedScalarStorage
open GeneralPaperEncodedBasisStorage (integerBits arrayFootprint arrayProfile)
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 18000000
set_option maxRecDepth 16384

abbrev Index (model : RationalCostModel) (W m k : ℕ) :=
  Fin ((prepare m k).K*GeneralPaperSourceQuantizedAnchorStorage.blockSize model W m k)

noncomputable def blockWindow (model : RationalCostModel) (W m k : ℕ) : ℕ :=
  GeneralPaperNativeBlockLabelStorage.window (B:=(prepare m k).K) (K:=(GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows+1)
    model W (GeneralPaperScoreScaleParameters.labels_positive m k)
    ⟨(GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows,by
      have h := GeneralPaperScoreScaleParameters.labels_positive m k
      change 0<(prepare m k).K at h
      nlinarith only [h]⟩

noncomputable def window (model : RationalCostModel) (W m k : ℕ) (active : Option (Index model W m k)) : ℕ :=
  blockWindow model W m k+(match active with
    | none => 0
    | some r => GeneralPaperNativeBlockLabelStorage.window model W (GeneralPaperSourceQuantizedAnchorStorage.block_positive model W m k) r)

theorem block_bounded (model : RationalCostModel) (W m k : ℕ) :
    GeneralPaperSourceQuantizedAnchorStorage.blockSize model W m k≤
      (GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows := by
  unfold GeneralPaperSourceQuantizedAnchorStorage.blockSize
  have h := (GeneralPaperNativeDivisibleColumns.blocks model.rat W
    (GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows (prepare m k).K
    (GeneralPaperScoreScaleParameters.labels_positive m k)).1.isLt
  omega

theorem index_bounded (model : RationalCostModel) (W m k : ℕ) (r : Index model W m k) :
    r.val≤(GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows := by
  exact r.isLt.le.trans_eq (GeneralPaperSourceQuantizedAnchorStorage.size_eq model W m k).symm

theorem native_entry {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (weights : FixedArrayTable m ℕ)
    (b : ℝ) (reciprocal : Bool) (j : Fin m) (r : Index model W m k) :
    (GeneralPaperNativeQuantizedLabels.entry model.rat W (GeneralPaperSourceQuantizedAnchorStorage.block_positive model W m k)
      (GeneralPaperSourceQuantizedAnchorStorage.order model W k Qv weights b reciprocal j) r).1.2=
        (GeneralPaperNativeBlockLabel.run model.rat W (GeneralPaperSourceQuantizedAnchorStorage.block_positive model W m k) r).1 := rfl

theorem source_divisions (model : RationalCostModel) (W m k : ℕ) :
    (∀ active,window model W m k active≤GeneralPaperSourceBlockDivisionStorageRates.sourceProfile model W m k) ∧
      (GeneralPaperNativeDivisibleColumns.blocks model.rat W
        (GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows (prepare m k).K
        (GeneralPaperScoreScaleParameters.labels_positive m k)).2≤
          GeneralPaperNativeBlockLabelStorage.price model W
            (GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows
            (GeneralPaperSourceBlockDivisionStorageRates.operandCap m k) ∧
      ∀ r : Index model W m k,
        (GeneralPaperNativeBlockLabel.run model.rat W (GeneralPaperSourceQuantizedAnchorStorage.block_positive model W m k) r).2≤
          GeneralPaperNativeBlockLabelStorage.price model W
            (GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows
            (GeneralPaperSourceBlockDivisionStorageRates.operandCap m k) := by
  let T := (GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows
  let K := (prepare m k).K
  let B := GeneralPaperSourceQuantizedAnchorStorage.blockSize model W m k
  have hK : 0<K := GeneralPaperScoreScaleParameters.labels_positive m k
  have hB : 0<B := GeneralPaperSourceQuantizedAnchorStorage.block_positive model W m k
  have hb := block_bounded model W m k
  have hkCap : K≤GeneralPaperSourceBlockDivisionStorageRates.operandCap m k := by
    unfold K GeneralPaperSourceBlockDivisionStorageRates.operandCap
    omega
  have hbCap : B≤GeneralPaperSourceBlockDivisionStorageRates.operandCap m k := by
    unfold GeneralPaperSourceBlockDivisionStorageRates.operandCap
    change B≤T+K+1
    change B≤T at hb
    omega
  let r : Fin ((T+1)*K) := ⟨T,by nlinarith only [hK]⟩
  have hBlock := GeneralPaperNativeBlockLabelStorage.bounded model W T hK r le_rfl
  have hBlock' : blockWindow model W m k≤GeneralPaperNativeBlockLabelStorage.profile model W T
      (GeneralPaperSourceBlockDivisionStorageRates.operandCap m k) :=
    hBlock.trans (GeneralPaperNativeBlockLabelStorage.profile_mono model W T T K _ le_rfl hkCap)
  have hLabel (s : Index model W m k) := (GeneralPaperNativeBlockLabelStorage.bounded model W T hB s
    (index_bounded model W m k s)).trans (GeneralPaperNativeBlockLabelStorage.profile_mono model W T T B _ le_rfl hbCap)
  refine ⟨?_,?_,?_⟩
  · intro active
    have hActive : (match active with | none => 0 | some s => GeneralPaperNativeBlockLabelStorage.window model W hB s)≤
        GeneralPaperNativeBlockLabelStorage.profile model W T (GeneralPaperSourceBlockDivisionStorageRates.operandCap m k) := by
      cases active with
      | none => exact Nat.zero_le _
      | some s => exact hLabel s
    change blockWindow model W m k+_≤_
    unfold GeneralPaperSourceBlockDivisionStorageRates.sourceProfile
    change _≤2*GeneralPaperNativeBlockLabelStorage.profile model W T (GeneralPaperSourceBlockDivisionStorageRates.operandCap m k)
    omega
  · have h := GeneralPaperNativeBlockLabelStorage.work model W T hK r le_rfl
    exact h.trans (GeneralPaperNativeBlockLabelStorage.price_mono model W T T K _ le_rfl hkCap)
  · intro s
    exact (GeneralPaperNativeBlockLabelStorage.work model W T hB s (index_bounded model W m k s)).trans
      (GeneralPaperNativeBlockLabelStorage.price_mono model W T T B _ le_rfl hbCap)

def AtBound {T m : ℕ} (model : RationalCostModel) (W k limit : ℕ) (b : ℝ) (reciprocal : Bool)
    (prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K)
    (state : State (m*((prepare m k).K-1)) (m*((prepare m k).K-1))) (resident parent : ℕ)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T (prepare m k).K))
    (values : GeneralPaperRetainedFieldValues.Values m) (own opposing : ℚ)
    (unnormalized : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T (prepare m k).K))
    (anchorSpace : Fin m → (count : ℕ) → count≤(prepare m k).K → ℕ)
    (sortSpace : Fin m → ℕ → ℕ → GeneralPaperSourceRepresentativeSortStorage.Active model W m k → ℕ)
    (materialSpace : Fin m → (count : ℕ) → count≤(GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows → ℕ)
    (divisionSpace : Option (Index model W m k) → ℕ) : Prop :=
  ∃ D F,GeneralPaperSourceColumnInputStorage.AtBound model W k D b reciprocal prep inputs state resident parent columns values own opposing unnormalized anchorSpace sortSpace materialSpace ∧
    (∀ active,divisionSpace active≤F) ∧ D+F≤limit

theorem bound_mono {T m : ℕ} (model : RationalCostModel) (W k : ℕ) (b : ℝ) (reciprocal : Bool)
    (prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K)
    (state : State (m*((prepare m k).K-1)) (m*((prepare m k).K-1))) (resident parent : ℕ)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T (prepare m k).K))
    (values : GeneralPaperRetainedFieldValues.Values m) (own opposing : ℚ) (unnormalized : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T (prepare m k).K)) (anchorSpace : Fin m → (count : ℕ) → count≤(prepare m k).K → ℕ) (sortSpace : Fin m → ℕ → ℕ → GeneralPaperSourceRepresentativeSortStorage.Active model W m k → ℕ) (materialSpace : Fin m → (count : ℕ) → count≤(GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows → ℕ) (divisionSpace : Option (Index model W m k) → ℕ) (B C : ℕ) (hBC : B≤C)
    (h : AtBound model W k B b reciprocal prep inputs state resident parent columns values own opposing unnormalized anchorSpace sortSpace materialSpace divisionSpace) :
    AtBound model W k C b reciprocal prep inputs state resident parent columns values own opposing unnormalized anchorSpace sortSpace materialSpace divisionSpace := by
  obtain ⟨D,F,hOld,hDivision,hSum⟩ := h
  exact ⟨D,F,hOld,hDivision,hSum.trans hBC⟩

theorem retained_divisions {T m : ℕ} (model : RationalCostModel) (W k limit : ℕ) (b : ℝ) (reciprocal : Bool)
    (prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K)
    (state : State (m*((prepare m k).K-1)) (m*((prepare m k).K-1))) (resident parent : ℕ)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T (prepare m k).K))
    (values : GeneralPaperRetainedFieldValues.Values m) (own opposing : ℚ)
    (unnormalized : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T (prepare m k).K))
    (anchorSpace : Fin m → (count : ℕ) → count≤(prepare m k).K → ℕ)
    (sortSpace : Fin m → ℕ → ℕ → GeneralPaperSourceRepresentativeSortStorage.Active model W m k → ℕ)
    (materialSpace : Fin m → (count : ℕ) → count≤(GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows → ℕ)
    (divisionSpace : Option (Index model W m k) → ℕ)
    (h : AtBound model W k limit b reciprocal prep inputs state resident parent columns values own opposing unnormalized anchorSpace sortSpace materialSpace divisionSpace) :
    ∀ j count hc l used copied active p fill hf division,
      resident+parent+anchorSpace j count hc+sortSpace l used copied active+materialSpace p fill hf+divisionSpace division≤limit := by
  obtain ⟨D,F,hOld,hDivision,hSum⟩ := h
  have hPrevious := GeneralPaperSourceColumnInputStorage.retained_materialization model W k D b reciprocal prep inputs state resident parent columns values own opposing unnormalized anchorSpace sortSpace materialSpace hOld
  intro j count hc l used copied active p fill hf division
  have hp := hPrevious j count hc l used copied active p fill hf
  have hs := hDivision division
  omega

theorem source_stage {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv)
    (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool)
    (hModify : (GeneralPaperProxyClassifier.classify m k b).choice.modify≠none)
    (hGuard : ¬(reciprocal=true ∧ (GeneralPaperProxyClassifier.classify m k b).choice.endpoint=0))
    (hW : 1≤W) (hK : binaryWordWidth ((prepare m k).K+1)≤W) (hM : binaryWordWidth (m+1)≤W)
    (hIndex : binaryWordWidth ((prepare m k).S+2)≤W) (hDim : binaryWordWidth (m*((prepare m k).K-1)+3)≤W)
    (hBatch : binaryWordWidth (((prepare m k).S+1)*((prepare m k).K*(prepare m k).K)+3)≤W)
    (hT : binaryWordWidth ((GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows+1)≤W)
    (hFinalIndex : binaryWordWidth ((prepare m k).S+4)≤W) :
    let prep := GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b reciprocal
    let v := GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs
    let f := (GeneralPaperProxyClassifier.classify m k b).choice.proxy
    let inputs := GeneralPaperSharedBasisInputs.prepare k prep v f.num f.den reciprocal
    ∀ state,Invariant prep.dictionary v (prepare m k).S prep.threshold inputs.controls.N inputs.betaN inputs.initialGrid le_rfl state →
      AtBound model W k (GeneralPaperSourceBlockDivisionStorageRates.reservation model W m k Qv) b reciprocal prep inputs state
        (GeneralPaperSourceEnclosingOwners.window model W k Qv hQv weights hp hs b reciprocal)
        (GeneralPaperSourceStrictConstructorStorage.parentWindow model W k Qv hQv weights hp hs b reciprocal)
        (GeneralPaperSourceEnclosingOwners.columns model W k Qv weights b reciprocal)
        (GeneralPaperRetainedFieldValues.run true model W Qv hQv weights hp hs).1
        (GeneralPaperInitializerPreparedPoint.ownBudget m k b reciprocal) (GeneralPaperInitializerPreparedPoint.opposingBudget m k b reciprocal)
        (GeneralPaperSourceDictionaryNormalizationStorage.quantized model W k Qv weights b reciprocal)
        (GeneralPaperSourceQuantizedAnchorStorage.window model W k Qv weights b reciprocal)
        (GeneralPaperSourceRepresentativeSortStorage.window model W k Qv weights b reciprocal)
        (GeneralPaperSourceColumnInputStorage.window model W k Qv weights b reciprocal)
        (window model W m k) := by
  dsimp only
  intro state inv
  have hOld := GeneralPaperSourceColumnInputStorage.source_stage model W k Qv hm hQv weights hp hs b hb reciprocal hModify hGuard
    hW hK hM hIndex hDim hBatch hT hFinalIndex state inv
  exact ⟨GeneralPaperSourceColumnInputStorageRates.reservation model W m k Qv,
    GeneralPaperSourceBlockDivisionStorageRates.sourceProfile model W m k,hOld,(source_divisions model W m k).1,le_rfl⟩

theorem actual_reached {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv)
    (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool)
    (hModify : (GeneralPaperProxyClassifier.classify m k b).choice.modify≠none)
    (hGuard : ¬(reciprocal=true ∧ (GeneralPaperProxyClassifier.classify m k b).choice.endpoint=0))
    (hW : 1≤W) (hK : binaryWordWidth ((prepare m k).K+1)≤W) (hM : binaryWordWidth (m+1)≤W)
    (hIndex : binaryWordWidth ((prepare m k).S+2)≤W) (hDim : binaryWordWidth (m*((prepare m k).K-1)+3)≤W)
    (hBatch : binaryWordWidth (((prepare m k).S+1)*((prepare m k).K*(prepare m k).K)+3)≤W)
    (hT : binaryWordWidth ((GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows+1)≤W)
    (hFinalIndex : binaryWordWidth ((prepare m k).S+4)≤W) :
    let prep := GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b reciprocal
    let v := GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs
    let f := (GeneralPaperProxyClassifier.classify m k b).choice.proxy
    let inputs := GeneralPaperSharedBasisInputs.prepare k prep v f.num f.den reciprocal
    ∃ state,(GeneralPaperBasisControllerBits.stages model W prep.dictionary.label inputs.matrix (prepare m k).S prep.threshold
      inputs.controls.N inputs.betaN inputs.initialGrid (m*((prepare m k).K-1)) le_rfl).1=some state ∧
      AtBound model W k (GeneralPaperSourceBlockDivisionStorageRates.reservation model W m k Qv) b reciprocal prep inputs state
        (GeneralPaperSourceEnclosingOwners.window model W k Qv hQv weights hp hs b reciprocal)
        (GeneralPaperSourceStrictConstructorStorage.parentWindow model W k Qv hQv weights hp hs b reciprocal)
        (GeneralPaperSourceEnclosingOwners.columns model W k Qv weights b reciprocal)
        (GeneralPaperRetainedFieldValues.run true model W Qv hQv weights hp hs).1
        (GeneralPaperInitializerPreparedPoint.ownBudget m k b reciprocal) (GeneralPaperInitializerPreparedPoint.opposingBudget m k b reciprocal)
        (GeneralPaperSourceDictionaryNormalizationStorage.quantized model W k Qv weights b reciprocal)
        (GeneralPaperSourceQuantizedAnchorStorage.window model W k Qv weights b reciprocal)
        (GeneralPaperSourceRepresentativeSortStorage.window model W k Qv weights b reciprocal)
        (GeneralPaperSourceColumnInputStorage.window model W k Qv weights b reciprocal)
        (window model W m k) := by
  obtain ⟨state,hr,hOld⟩ := GeneralPaperSourceColumnInputStorage.actual_reached model W k Qv hm hQv weights hp hs b hb reciprocal hModify hGuard
    hW hK hM hIndex hDim hBatch hT hFinalIndex
  exact ⟨state,hr,GeneralPaperSourceColumnInputStorageRates.reservation model W m k Qv,
    GeneralPaperSourceBlockDivisionStorageRates.sourceProfile model W m k,hOld,(source_divisions model W m k).1,le_rfl⟩

theorem guard_stage {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (_hm : 0<m) (hQv : 0<Qv)
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
      GeneralPaperSourceBlockDivisionStorageRates.sourceProfile model W m k≤
        GeneralPaperSourceBlockDivisionStorageRates.reservation model W m k Qv := by
  have hOld := GeneralPaperSourceColumnInputStorage.guard_stage model W k Qv _hm hQv weights hp hs b hb reciprocal hModify hGuard hW hK hM hIndex
  exact Nat.add_le_add_right hOld _

end Blotto.GeneralPaperSourceBlockDivisionStorage
