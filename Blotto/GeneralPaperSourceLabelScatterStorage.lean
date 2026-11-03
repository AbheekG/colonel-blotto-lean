import Blotto.GeneralPaperSourceLabelScatterStorageRates
import Blotto.GeneralPaperRetainedSourceColumnBits

/-! Actual native label scatter through the original retained stable
order. Every independent initial/scatter cursor and active division call
has full buffer/recursive-frame storage. Literal label/rank identities and
native work join all preceding source and strict/endpoint contracts. -/
namespace Blotto.GeneralPaperSourceLabelScatterStorage
open RationalOrderCell GeneralPaperProxyParameters GeneralPaperBasisStoredProducts
open GeneralPaperBasisState GeneralPaperBasisInvariant GeneralPaperEncodedScalarStorage
open GeneralPaperEncodedBasisStorage (integerBits arrayFootprint arrayProfile)
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 18000000
set_option maxRecDepth 16384

noncomputable def window {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (weights : FixedArrayTable m ℕ)
    (b : ℝ) (reciprocal : Bool) (j : Fin m)
    (initialCount : ℕ) (hi : initialCount≤(GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows)
    (count : ℕ) (hc : count≤(GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows)
    (active : Option (GeneralPaperSourceBlockDivisionStorage.Index model W m k)) : ℕ :=
  GeneralPaperQuantizedLabelScatterStorage.window (K:=(prepare m k).K) model W (GeneralPaperScoreScaleParameters.labels_positive m k)
    (GeneralPaperSourceQuantizedAnchorStorage.block_positive model W m k)
    (GeneralPaperSourceQuantizedAnchorStorage.order model W k Qv weights b reciprocal j)
    initialCount (by rw [←GeneralPaperSourceQuantizedAnchorStorage.size_eq model W m k];exact hi)
    count (by rw [←GeneralPaperSourceQuantizedAnchorStorage.size_eq model W m k];exact hc) active

theorem native_labels {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (weights : FixedArrayTable m ℕ)
    (b : ℝ) (reciprocal : Bool) (j : Fin m) :
    (GeneralPaperNativeQuantizedLabels.run model.rat (fun w => w) W (GeneralPaperScoreScaleParameters.labels_positive m k)
      (GeneralPaperSourceQuantizedAnchorStorage.block_positive model W m k)
      (GeneralPaperSourceQuantizedAnchorStorage.order model W k Qv weights b reciprocal j)).1=
        (GeneralPaperNativeQuantizedColumn.run model.rat (fun w => w) W (GeneralPaperScoreScaleParameters.labels_positive m k)
          (GeneralPaperSourceQuantizedAnchorStorage.block_positive model W m k)
          (GeneralPaperSourceQuantizedAnchorStorage.values model W k Qv weights b reciprocal j)).1.labels := rfl

theorem native_rank {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (weights : FixedArrayTable m ℕ)
    (b : ℝ) (reciprocal : Bool) (j : Fin m) (r : GeneralPaperSourceBlockDivisionStorage.Index model W m k) :
    (GeneralPaperNativeQuantizedLabels.run model.rat (fun w => w) W (GeneralPaperScoreScaleParameters.labels_positive m k)
      (GeneralPaperSourceQuantizedAnchorStorage.block_positive model W m k)
      (GeneralPaperSourceQuantizedAnchorStorage.order model W k Qv weights b reciprocal j)).1.read
        ((GeneralPaperSourceQuantizedAnchorStorage.order model W k Qv weights b reciprocal j).read r)=
          GeneralPaperQuantileBlocks.block (GeneralPaperSourceQuantizedAnchorStorage.block_positive model W m k) r := by
  apply GeneralPaperNativeQuantizedLabels.read_rank
  unfold GeneralPaperSourceQuantizedAnchorStorage.order
  rw [GeneralPaperNativeRepresentativeSort.data]
  exact GeneralPaperRowSort.order_injective _

theorem source_labels {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (weights : FixedArrayTable m ℕ)
    (b : ℝ) (reciprocal : Bool) (hW : 1≤W)
    (hScatter : binaryWordWidth ((GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows+
      (GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows+1)≤W) :
    (∀ j initialCount hi count hc active,window model W k Qv weights b reciprocal j initialCount hi count hc active≤
      GeneralPaperSourceLabelScatterStorageRates.sourceProfile model W m k) ∧
      ∀ j,(GeneralPaperNativeQuantizedLabels.run model.rat (fun w => w) W (GeneralPaperScoreScaleParameters.labels_positive m k)
        (GeneralPaperSourceQuantizedAnchorStorage.block_positive model W m k)
        (GeneralPaperSourceQuantizedAnchorStorage.order model W k Qv weights b reciprocal j)).2≤
          GeneralPaperQuantizedLabelScatterStorage.price model W
            (GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows
            (GeneralPaperSourceLabelScatterStorageRates.operandCap m k) := by
  have hIndex : binaryWordWidth ((prepare m k).K*GeneralPaperSourceQuantizedAnchorStorage.blockSize model W m k+
      (prepare m k).K*GeneralPaperSourceQuantizedAnchorStorage.blockSize model W m k+1)≤W := by
    rw [←GeneralPaperSourceQuantizedAnchorStorage.size_eq model W m k]
    exact hScatter
  have hB := GeneralPaperSourceBlockDivisionStorage.block_bounded model W m k
  have hCap : GeneralPaperSourceQuantizedAnchorStorage.blockSize model W m k≤GeneralPaperSourceLabelScatterStorageRates.operandCap m k := by
    unfold GeneralPaperSourceLabelScatterStorageRates.operandCap
    omega
  refine ⟨?_,?_⟩
  · intro j initialCount hi count hc active
    have h := GeneralPaperQuantizedLabelScatterStorage.bounded (K:=(prepare m k).K) model W
      (GeneralPaperScoreScaleParameters.labels_positive m k) (GeneralPaperSourceQuantizedAnchorStorage.block_positive model W m k)
      (GeneralPaperSourceQuantizedAnchorStorage.order model W k Qv weights b reciprocal j) hW hIndex
      initialCount (by rw [←GeneralPaperSourceQuantizedAnchorStorage.size_eq model W m k];exact hi)
      count (by rw [←GeneralPaperSourceQuantizedAnchorStorage.size_eq model W m k];exact hc) active
    apply h.trans
    rw [←GeneralPaperSourceQuantizedAnchorStorage.size_eq model W m k]
    exact GeneralPaperQuantizedLabelScatterStorage.profile_mono model W _ _ _ _ hCap
  · intro j
    have h := GeneralPaperQuantizedLabelScatterStorage.work (K:=(prepare m k).K) model W
      (GeneralPaperScoreScaleParameters.labels_positive m k) (GeneralPaperSourceQuantizedAnchorStorage.block_positive model W m k)
      (GeneralPaperSourceQuantizedAnchorStorage.order model W k Qv weights b reciprocal j) hW hIndex
    apply h.trans
    rw [←GeneralPaperSourceQuantizedAnchorStorage.size_eq model W m k]
    exact GeneralPaperQuantizedLabelScatterStorage.price_mono model W _ _ _ hCap

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
    (divisionSpace : Option (GeneralPaperSourceBlockDivisionStorage.Index model W m k) → ℕ)
    (scatterSpace : Fin m → (initialCount : ℕ) → initialCount≤(GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows → (count : ℕ) → count≤(GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows → Option (GeneralPaperSourceBlockDivisionStorage.Index model W m k) → ℕ) : Prop :=
  ∃ D F,GeneralPaperSourceBlockDivisionStorage.AtBound model W k D b reciprocal prep inputs state resident parent columns values own opposing unnormalized anchorSpace sortSpace materialSpace divisionSpace ∧
    (∀ j initialCount hi count hc active,scatterSpace j initialCount hi count hc active≤F) ∧ D+F≤limit

theorem bound_mono {T m : ℕ} (model : RationalCostModel) (W k : ℕ) (b : ℝ) (reciprocal : Bool)
    (prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K)
    (state : State (m*((prepare m k).K-1)) (m*((prepare m k).K-1))) (resident parent : ℕ)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T (prepare m k).K))
    (values : GeneralPaperRetainedFieldValues.Values m) (own opposing : ℚ) (unnormalized : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T (prepare m k).K)) (anchorSpace : Fin m → (count : ℕ) → count≤(prepare m k).K → ℕ) (sortSpace : Fin m → ℕ → ℕ → GeneralPaperSourceRepresentativeSortStorage.Active model W m k → ℕ) (materialSpace : Fin m → (count : ℕ) → count≤(GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows → ℕ) (divisionSpace : Option (GeneralPaperSourceBlockDivisionStorage.Index model W m k) → ℕ) (scatterSpace : Fin m → (initialCount : ℕ) → initialCount≤(GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows → (count : ℕ) → count≤(GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows → Option (GeneralPaperSourceBlockDivisionStorage.Index model W m k) → ℕ) (B C : ℕ) (hBC : B≤C)
    (h : AtBound model W k B b reciprocal prep inputs state resident parent columns values own opposing unnormalized anchorSpace sortSpace materialSpace divisionSpace scatterSpace) :
    AtBound model W k C b reciprocal prep inputs state resident parent columns values own opposing unnormalized anchorSpace sortSpace materialSpace divisionSpace scatterSpace := by
  obtain ⟨D,F,hOld,hScatter,hSum⟩ := h
  exact ⟨D,F,hOld,hScatter,hSum.trans hBC⟩

theorem retained_scatter {T m : ℕ} (model : RationalCostModel) (W k limit : ℕ) (b : ℝ) (reciprocal : Bool)
    (prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K)
    (state : State (m*((prepare m k).K-1)) (m*((prepare m k).K-1))) (resident parent : ℕ)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T (prepare m k).K))
    (values : GeneralPaperRetainedFieldValues.Values m) (own opposing : ℚ)
    (unnormalized : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T (prepare m k).K))
    (anchorSpace : Fin m → (count : ℕ) → count≤(prepare m k).K → ℕ)
    (sortSpace : Fin m → ℕ → ℕ → GeneralPaperSourceRepresentativeSortStorage.Active model W m k → ℕ)
    (materialSpace : Fin m → (count : ℕ) → count≤(GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows → ℕ)
    (divisionSpace : Option (GeneralPaperSourceBlockDivisionStorage.Index model W m k) → ℕ)
    (scatterSpace : Fin m → (initialCount : ℕ) → initialCount≤(GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows → (count : ℕ) → count≤(GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows → Option (GeneralPaperSourceBlockDivisionStorage.Index model W m k) → ℕ)
    (h : AtBound model W k limit b reciprocal prep inputs state resident parent columns values own opposing unnormalized anchorSpace sortSpace materialSpace divisionSpace scatterSpace) :
    ∀ j count hc l used copied active p fill hf division q initialCount hi scatterCount hs scatter,
      resident+parent+anchorSpace j count hc+sortSpace l used copied active+materialSpace p fill hf+divisionSpace division+
        scatterSpace q initialCount hi scatterCount hs scatter≤limit := by
  obtain ⟨D,F,hOld,hScatter,hSum⟩ := h
  have hPrevious := GeneralPaperSourceBlockDivisionStorage.retained_divisions model W k D b reciprocal prep inputs state resident parent columns values own opposing unnormalized anchorSpace sortSpace materialSpace divisionSpace hOld
  intro j count hc l used copied active p fill hf division q initialCount hi scatterCount hs scatter
  have hp := hPrevious j count hc l used copied active p fill hf division
  have hsc := hScatter q initialCount hi scatterCount hs scatter
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
    (hScatter : binaryWordWidth ((GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows+(GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows+1)≤W)
    (hFinalIndex : binaryWordWidth ((prepare m k).S+4)≤W) :
    let prep := GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b reciprocal
    let v := GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs
    let f := (GeneralPaperProxyClassifier.classify m k b).choice.proxy
    let inputs := GeneralPaperSharedBasisInputs.prepare k prep v f.num f.den reciprocal
    ∀ state,Invariant prep.dictionary v (prepare m k).S prep.threshold inputs.controls.N inputs.betaN inputs.initialGrid le_rfl state →
      AtBound model W k (GeneralPaperSourceLabelScatterStorageRates.reservation model W m k Qv) b reciprocal prep inputs state
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
        (window model W k Qv weights b reciprocal) := by
  dsimp only
  intro state inv
  have hOld := GeneralPaperSourceBlockDivisionStorage.source_stage model W k Qv hm hQv weights hp hs b hb reciprocal hModify hGuard
    hW hK hM hIndex hDim hBatch hT hFinalIndex state inv
  exact ⟨GeneralPaperSourceBlockDivisionStorageRates.reservation model W m k Qv,
    GeneralPaperSourceLabelScatterStorageRates.sourceProfile model W m k,hOld,(source_labels model W k Qv weights b reciprocal hW hScatter).1,le_rfl⟩

theorem actual_reached {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv)
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
      AtBound model W k (GeneralPaperSourceLabelScatterStorageRates.reservation model W m k Qv) b reciprocal prep inputs state
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
        (window model W k Qv weights b reciprocal) := by
  obtain ⟨state,hr,hOld⟩ := GeneralPaperSourceBlockDivisionStorage.actual_reached model W k Qv hm hQv weights hp hs b hb reciprocal hModify hGuard
    hW hK hM hIndex hDim hBatch hT hFinalIndex
  exact ⟨state,hr,GeneralPaperSourceBlockDivisionStorageRates.reservation model W m k Qv,
    GeneralPaperSourceLabelScatterStorageRates.sourceProfile model W m k,hOld,(source_labels model W k Qv weights b reciprocal hW hScatter).1,le_rfl⟩

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
      GeneralPaperSourceBlockDivisionStorageRates.sourceProfile model W m k+
      GeneralPaperSourceLabelScatterStorageRates.sourceProfile model W m k≤
        GeneralPaperSourceLabelScatterStorageRates.reservation model W m k Qv := by
  have hOld := GeneralPaperSourceBlockDivisionStorage.guard_stage model W k Qv _hm hQv weights hp hs b hb reciprocal hModify hGuard hW hK hM hIndex
  exact Nat.add_le_add_right hOld _

end Blotto.GeneralPaperSourceLabelScatterStorage
