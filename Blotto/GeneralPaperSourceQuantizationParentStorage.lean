import Blotto.GeneralPaperSourceQuantizationParentStorageRates
import Blotto.GeneralPaperRetainedSourceColumnBits

/-! Complete native quantized-column/matrix/divisible-column caller
storage on the original source rows, joined to all actual earlier child
and strict/endpoint contracts. Physical outputs are precisely the columns
already consumed by normalization; no source or quantizer replay executes. -/
namespace Blotto.GeneralPaperSourceQuantizationParentStorage
open RationalOrderCell GeneralPaperProxyParameters GeneralPaperBasisStoredProducts
open GeneralPaperBasisState GeneralPaperBasisInvariant GeneralPaperEncodedScalarStorage
open GeneralPaperEncodedBasisStorage (integerBits arrayFootprint arrayProfile)
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 18000000
set_option maxRecDepth 16384

noncomputable def window {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (weights : FixedArrayTable m ℕ)
    (b : ℝ) (reciprocal : Bool) (outer : ℕ) (ho : outer≤m) (active : Option (Fin m)) : ℕ :=
  GeneralPaperDivisibleColumnsParentStorage.window model W
    (GeneralPaperTrajectoryParameters.rows_positive (alphabet m k).lambda k) (GeneralPaperScoreScaleParameters.labels_positive m k)
    (GeneralPaperTrajectoryParameters.labels_divide_rows m (alphabet m k).lambda k)
    (GeneralPaperSourceInitializer.sourceRows k Qv weights b reciprocal) outer ho active

theorem native_quantized {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (weights : FixedArrayTable m ℕ)
    (b : ℝ) (reciprocal : Bool) :
    (GeneralPaperNativeDivisibleColumns.run model.rat (fun w => w) W
      (GeneralPaperTrajectoryParameters.rows_positive (alphabet m k).lambda k) (GeneralPaperScoreScaleParameters.labels_positive m k)
      (GeneralPaperTrajectoryParameters.labels_divide_rows m (alphabet m k).lambda k)
      (GeneralPaperSourceInitializer.sourceRows k Qv weights b reciprocal)).1=
        GeneralPaperSourceDictionaryNormalizationStorage.quantized model W k Qv weights b reciprocal := rfl

theorem native_normalized {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (weights : FixedArrayTable m ℕ)
    (b : ℝ) (reciprocal : Bool) :
    (GeneralPaperNativeDictionaryNormalize.run model.rat (fun w => w) W
      (GeneralPaperInitializerPreparedPoint.ownBudget m k b reciprocal)
      (GeneralPaperSourceDictionaryNormalizationStorage.quantized model W k Qv weights b reciprocal)).1=
        GeneralPaperSourceEnclosingOwners.columns model W k Qv weights b reciprocal := rfl

theorem source_parents {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (weights : FixedArrayTable m ℕ)
    (b : ℝ) (reciprocal : Bool) (hW : 1≤W) (hK : binaryWordWidth ((prepare m k).K+1)≤W) (hM : binaryWordWidth (m+1)≤W)
    (hScatter : binaryWordWidth ((GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows+
      (GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows+1)≤W) :
    (∀ outer ho active,window model W k Qv weights b reciprocal outer ho active≤
      GeneralPaperSourceQuantizationParentStorageRates.sourceProfile model W m k) ∧
      (GeneralPaperNativeDivisibleColumns.run model.rat (fun w => w) W
        (GeneralPaperTrajectoryParameters.rows_positive (alphabet m k).lambda k) (GeneralPaperScoreScaleParameters.labels_positive m k)
        (GeneralPaperTrajectoryParameters.labels_divide_rows m (alphabet m k).lambda k)
        (GeneralPaperSourceInitializer.sourceRows k Qv weights b reciprocal)).2≤
          GeneralPaperDivisibleColumnsParentStorage.price model W
            (GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows m (prepare m k).K
            (GeneralPaperSourceQuantizationParentStorageRates.operandCap m k) (GeneralPaperSourceQuantizationParentStorageRates.operandWidth m k) := by
  let R := GeneralPaperSourceQuantizationParentStorageRates.operandWidth m k
  have hR : 3≤R := by
    have h := binaryWordWidth_pos (alphabet m k).C
    unfold R GeneralPaperSourceQuantizationParentStorageRates.operandWidth GeneralPaperSourceScoreHeights.anchorHeight
    omega
  have hRows (i j) : rationalWordWidth (((GeneralPaperSourceInitializer.sourceRows k Qv weights b reciprocal).read i).read j)≤R := by
    have h := rationalWordWidth_of_height (GeneralPaperSourceScoreHeights.rows_height k Qv weights b reciprocal i j)
    unfold R GeneralPaperSourceQuantizationParentStorageRates.operandWidth GeneralPaperSourceScoreHeights.anchorHeight
    omega
  have hB : GeneralPaperDivisibleColumnsParentStorage.blockSize model W
      (GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows (prepare m k).K
      (GeneralPaperScoreScaleParameters.labels_positive m k)≤GeneralPaperSourceQuantizationParentStorageRates.operandCap m k := by
    have h := GeneralPaperDivisibleColumnsParentStorage.block_bounded model W
      (GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows (prepare m k).K
      (GeneralPaperScoreScaleParameters.labels_positive m k)
    unfold GeneralPaperSourceQuantizationParentStorageRates.operandCap
    omega
  refine ⟨?_,?_⟩
  · intro outer ho active
    exact GeneralPaperDivisibleColumnsParentStorage.bounded (K:=(prepare m k).K) model W R
      (GeneralPaperSourceQuantizationParentStorageRates.operandCap m k)
      (GeneralPaperTrajectoryParameters.rows_positive (alphabet m k).lambda k) (GeneralPaperScoreScaleParameters.labels_positive m k)
      (GeneralPaperTrajectoryParameters.labels_divide_rows m (alphabet m k).lambda k)
      (GeneralPaperSourceInitializer.sourceRows k Qv weights b reciprocal) hR hRows hB hW hScatter hK hM outer ho active
  · exact GeneralPaperDivisibleColumnsParentStorage.work (K:=(prepare m k).K) model W R
      (GeneralPaperSourceQuantizationParentStorageRates.operandCap m k)
      (GeneralPaperTrajectoryParameters.rows_positive (alphabet m k).lambda k) (GeneralPaperScoreScaleParameters.labels_positive m k)
      (GeneralPaperTrajectoryParameters.labels_divide_rows m (alphabet m k).lambda k)
      (GeneralPaperSourceInitializer.sourceRows k Qv weights b reciprocal) hRows hB hW hScatter hK hM

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
    (scatterSpace : Fin m → (initialCount : ℕ) → initialCount≤(GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows → (count : ℕ) → count≤(GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows → Option (GeneralPaperSourceBlockDivisionStorage.Index model W m k) → ℕ)
    (quantizationSpace : (outer : ℕ) → outer≤m → Option (Fin m) → ℕ) : Prop :=
  ∃ D F,GeneralPaperSourceLabelScatterStorage.AtBound model W k D b reciprocal prep inputs state resident parent columns values own opposing unnormalized anchorSpace sortSpace materialSpace divisionSpace scatterSpace ∧
    (∀ outer ho active,quantizationSpace outer ho active≤F) ∧ D+F≤limit

theorem bound_mono {T m : ℕ} (model : RationalCostModel) (W k : ℕ) (b : ℝ) (reciprocal : Bool)
    (prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K)
    (state : State (m*((prepare m k).K-1)) (m*((prepare m k).K-1))) (resident parent : ℕ)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T (prepare m k).K))
    (values : GeneralPaperRetainedFieldValues.Values m) (own opposing : ℚ) (unnormalized : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T (prepare m k).K)) (anchorSpace : Fin m → (count : ℕ) → count≤(prepare m k).K → ℕ) (sortSpace : Fin m → ℕ → ℕ → GeneralPaperSourceRepresentativeSortStorage.Active model W m k → ℕ) (materialSpace : Fin m → (count : ℕ) → count≤(GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows → ℕ) (divisionSpace : Option (GeneralPaperSourceBlockDivisionStorage.Index model W m k) → ℕ) (scatterSpace : Fin m → (initialCount : ℕ) → initialCount≤(GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows → (count : ℕ) → count≤(GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows → Option (GeneralPaperSourceBlockDivisionStorage.Index model W m k) → ℕ) (quantizationSpace : (outer : ℕ) → outer≤m → Option (Fin m) → ℕ) (B C : ℕ) (hBC : B≤C)
    (h : AtBound model W k B b reciprocal prep inputs state resident parent columns values own opposing unnormalized anchorSpace sortSpace materialSpace divisionSpace scatterSpace quantizationSpace) :
    AtBound model W k C b reciprocal prep inputs state resident parent columns values own opposing unnormalized anchorSpace sortSpace materialSpace divisionSpace scatterSpace quantizationSpace := by
  obtain ⟨D,F,hOld,hParents,hSum⟩ := h
  exact ⟨D,F,hOld,hParents,hSum.trans hBC⟩

theorem retained_parents {T m : ℕ} (model : RationalCostModel) (W k limit : ℕ) (b : ℝ) (reciprocal : Bool)
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
    (quantizationSpace : (outer : ℕ) → outer≤m → Option (Fin m) → ℕ)
    (h : AtBound model W k limit b reciprocal prep inputs state resident parent columns values own opposing unnormalized anchorSpace sortSpace materialSpace divisionSpace scatterSpace quantizationSpace) :
    ∀ j count hc l used copied active p fill hf division q initialCount hi scatterCount hs scatter outer ho field,
      resident+parent+anchorSpace j count hc+sortSpace l used copied active+materialSpace p fill hf+divisionSpace division+
        scatterSpace q initialCount hi scatterCount hs scatter+quantizationSpace outer ho field≤limit := by
  obtain ⟨D,F,hOld,hParents,hSum⟩ := h
  have hPrevious := GeneralPaperSourceLabelScatterStorage.retained_scatter model W k D b reciprocal prep inputs state resident parent columns values own opposing unnormalized anchorSpace sortSpace materialSpace divisionSpace scatterSpace hOld
  intro j count hc l used copied active p fill hf division q initialCount hi scatterCount hs scatter outer ho field
  have hp := hPrevious j count hc l used copied active p fill hf division q initialCount hi scatterCount hs scatter
  have hq := hParents outer ho field
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
      AtBound model W k (GeneralPaperSourceQuantizationParentStorageRates.reservation model W m k Qv) b reciprocal prep inputs state
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
        (window model W k Qv weights b reciprocal) := by
  dsimp only
  intro state inv
  have hOld := GeneralPaperSourceLabelScatterStorage.source_stage model W k Qv hm hQv weights hp hs b hb reciprocal hModify hGuard
    hW hK hM hIndex hDim hBatch hT hScatter hFinalIndex state inv
  exact ⟨GeneralPaperSourceLabelScatterStorageRates.reservation model W m k Qv,
    GeneralPaperSourceQuantizationParentStorageRates.sourceProfile model W m k,hOld,(source_parents model W k Qv weights b reciprocal hW hK hM hScatter).1,le_rfl⟩

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
      AtBound model W k (GeneralPaperSourceQuantizationParentStorageRates.reservation model W m k Qv) b reciprocal prep inputs state
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
        (window model W k Qv weights b reciprocal) := by
  obtain ⟨state,hr,hOld⟩ := GeneralPaperSourceLabelScatterStorage.actual_reached model W k Qv hm hQv weights hp hs b hb reciprocal hModify hGuard
    hW hK hM hIndex hDim hBatch hT hScatter hFinalIndex
  exact ⟨state,hr,GeneralPaperSourceLabelScatterStorageRates.reservation model W m k Qv,
    GeneralPaperSourceQuantizationParentStorageRates.sourceProfile model W m k,hOld,(source_parents model W k Qv weights b reciprocal hW hK hM hScatter).1,le_rfl⟩

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
      GeneralPaperSourceLabelScatterStorageRates.sourceProfile model W m k+
      GeneralPaperSourceQuantizationParentStorageRates.sourceProfile model W m k≤
        GeneralPaperSourceQuantizationParentStorageRates.reservation model W m k Qv := by
  have hOld := GeneralPaperSourceLabelScatterStorage.guard_stage model W k Qv _hm hQv weights hp hs b hb reciprocal hModify hGuard hW hK hM hIndex
  exact Nat.add_le_add_right hOld _

end Blotto.GeneralPaperSourceQuantizationParentStorage
