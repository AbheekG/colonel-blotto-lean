import Blotto.GeneralPaperSourceQuantizedAnchorStorageRates
import Blotto.GeneralPaperRetainedSourceColumnBits

/-! Actual previous-block anchor construction after retained source
column materialization and native stable sorting. Native computed block
size and original source rows derive every word/payload premise. No sort,
source or quotient replay executes in these erased lifetime observers. -/
namespace Blotto.GeneralPaperSourceQuantizedAnchorStorage
open RationalOrderCell GeneralPaperProxyParameters GeneralPaperBasisStoredProducts
open GeneralPaperBasisState GeneralPaperBasisInvariant GeneralPaperEncodedScalarStorage
open GeneralPaperEncodedBasisStorage (integerBits arrayFootprint arrayProfile)
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 18000000
set_option maxRecDepth 16384

noncomputable def blockSize (model : RationalCostModel) (W m k : ℕ) : ℕ :=
  (GeneralPaperNativeDivisibleColumns.blocks model.rat W
    (GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows (prepare m k).K
    (GeneralPaperScoreScaleParameters.labels_positive m k)).1.val

theorem size_eq (model : RationalCostModel) (W m k : ℕ) :
    (GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows=(prepare m k).K*blockSize model W m k := by
  unfold blockSize
  erw [GeneralPaperNativeDivisibleColumns.blocks_data]
  exact GeneralPaperRowQuantizer.divisor_size (GeneralPaperTrajectoryParameters.labels_divide_rows m (alphabet m k).lambda k)

theorem block_positive (model : RationalCostModel) (W m k : ℕ) : 0<blockSize model W m k := by
  unfold blockSize
  erw [GeneralPaperNativeDivisibleColumns.blocks_data]
  exact GeneralPaperRowQuantizer.divisor_block_pos (GeneralPaperTrajectoryParameters.rows_positive (alphabet m k).lambda k)
    (GeneralPaperScoreScaleParameters.labels_positive m k) (GeneralPaperTrajectoryParameters.labels_divide_rows m (alphabet m k).lambda k)

noncomputable def values {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (weights : FixedArrayTable m ℕ)
    (b : ℝ) (reciprocal : Bool) (j : Fin m) : FixedArrayTable ((prepare m k).K*blockSize model W m k) ℚ :=
  (GeneralPaperNativeQuantizedMatrix.columnInput (fun w => w) W
    (GeneralPaperRowQuantizer.castRows (size_eq model W m k) (GeneralPaperSourceInitializer.sourceRows k Qv weights b reciprocal)) j).1

noncomputable def order {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (weights : FixedArrayTable m ℕ)
    (b : ℝ) (reciprocal : Bool) (j : Fin m) :=
  (GeneralPaperNativeRepresentativeSort.run model.rat (fun w => w) W (values model W k Qv weights b reciprocal j)).1

noncomputable def window {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (weights : FixedArrayTable m ℕ)
    (b : ℝ) (reciprocal : Bool) (j : Fin m) (count : ℕ) (hc : count≤(prepare m k).K) : ℕ :=
  GeneralPaperQuantizedAnchorStorage.window model W (block_positive model W m k)
    (order model W k Qv weights b reciprocal j) (values model W k Qv weights b reciprocal j) count hc

theorem native_anchors {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (weights : FixedArrayTable m ℕ)
    (b : ℝ) (reciprocal : Bool) (j : Fin m) :
    (GeneralPaperNativeQuantizedAnchors.run model.rat (fun w => w) W (block_positive model W m k)
      (order model W k Qv weights b reciprocal j) (values model W k Qv weights b reciprocal j)).1=
      (GeneralPaperNativeQuantizedColumn.run model.rat (fun w => w) W (GeneralPaperScoreScaleParameters.labels_positive m k)
        (block_positive model W m k) (values model W k Qv weights b reciprocal j)).1.anchors := rfl

theorem source_anchors {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (weights : FixedArrayTable m ℕ)
    (b : ℝ) (reciprocal : Bool) (hW : 1≤W) (hK : binaryWordWidth ((prepare m k).K+1)≤W) :
    (∀ j count (hc : count≤(prepare m k).K),window model W k Qv weights b reciprocal j count hc≤
      GeneralPaperSourceQuantizedAnchorStorageRates.sourceProfile model W m k) ∧
      ∀ j,(GeneralPaperNativeQuantizedAnchors.run model.rat (fun w => w) W (block_positive model W m k)
        (order model W k Qv weights b reciprocal j) (values model W k Qv weights b reciprocal j)).2≤
          GeneralPaperQuantizedAnchorStorage.price model W (GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows (prepare m k).K := by
  let R := GeneralPaperSourceQuantizedAnchorStorageRates.operandWidth m k
  have hR : 3≤R := by
    have h := binaryWordWidth_pos (alphabet m k).C
    unfold R GeneralPaperSourceQuantizedAnchorStorageRates.operandWidth GeneralPaperSourceScoreHeights.anchorHeight
    omega
  have hRows (i l) : rationalWordWidth (((GeneralPaperSourceInitializer.sourceRows k Qv weights b reciprocal).read i).read l)≤R := by
    have h := rationalWordWidth_of_height (GeneralPaperSourceScoreHeights.rows_height k Qv weights b reciprocal i l)
    unfold R GeneralPaperSourceQuantizedAnchorStorageRates.operandWidth GeneralPaperSourceScoreHeights.anchorHeight
    omega
  have hValues (j i) : rationalWordWidth ((values model W k Qv weights b reciprocal j).read i)≤R := by
    unfold values
    rw [GeneralPaperNativeQuantizedMatrix.input_data,GeneralPaperRowQuantizer.columnInput,FixedArrayTable.read_ofFn]
    exact GeneralPaperNativeDivisibleColumns.cast_words (size_eq model W m k) _ R hRows i j
  refine ⟨?_,?_⟩
  · intro j count hc
    have h := GeneralPaperQuantizedAnchorStorage.bounded (K:=(prepare m k).K) model W R (GeneralPaperScoreScaleParameters.labels_positive m k)
      (block_positive model W m k) (order model W k Qv weights b reciprocal j) (values model W k Qv weights b reciprocal j)
      hR (hValues j) hW hK count hc
    apply h.trans
    rw [←size_eq model W m k]
    exact Nat.le_refl _

  · intro j
    have h := GeneralPaperQuantizedAnchorStorage.work (K:=(prepare m k).K) model W (GeneralPaperScoreScaleParameters.labels_positive m k)
      (block_positive model W m k) (order model W k Qv weights b reciprocal j) (values model W k Qv weights b reciprocal j) hW hK
    apply h.trans
    rw [←size_eq model W m k]


def AtBound {T m : ℕ} (model : RationalCostModel) (W k limit : ℕ) (b : ℝ) (reciprocal : Bool)
    (prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K)
    (state : State (m*((prepare m k).K-1)) (m*((prepare m k).K-1))) (resident parent : ℕ)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T (prepare m k).K))
    (values : GeneralPaperRetainedFieldValues.Values m) (own opposing : ℚ)
    (unnormalized : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T (prepare m k).K))
    (anchorSpace : Fin m → (count : ℕ) → count≤(prepare m k).K → ℕ) : Prop :=
  ∃ D F,GeneralPaperSourceDictionaryNormalizationStorage.AtBound model W k D b reciprocal prep inputs state resident parent columns values own opposing unnormalized ∧
    (∀ j count hc,anchorSpace j count hc≤F) ∧ D+F≤limit

theorem bound_mono {T m : ℕ} (model : RationalCostModel) (W k : ℕ) (b : ℝ) (reciprocal : Bool)
    (prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K)
    (state : State (m*((prepare m k).K-1)) (m*((prepare m k).K-1))) (resident parent : ℕ)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T (prepare m k).K))
    (values : GeneralPaperRetainedFieldValues.Values m) (own opposing : ℚ) (unnormalized : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T (prepare m k).K)) (anchorSpace : Fin m → (count : ℕ) → count≤(prepare m k).K → ℕ) (B C : ℕ) (hBC : B≤C)
    (h : AtBound model W k B b reciprocal prep inputs state resident parent columns values own opposing unnormalized anchorSpace) :
    AtBound model W k C b reciprocal prep inputs state resident parent columns values own opposing unnormalized anchorSpace := by
  obtain ⟨D,F,hOld,hAnchors,hSum⟩ := h
  exact ⟨D,F,hOld,hAnchors,hSum.trans hBC⟩

theorem retained_anchors {T m : ℕ} (model : RationalCostModel) (W k limit : ℕ) (b : ℝ) (reciprocal : Bool)
    (prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K)
    (state : State (m*((prepare m k).K-1)) (m*((prepare m k).K-1))) (resident parent : ℕ)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T (prepare m k).K))
    (values : GeneralPaperRetainedFieldValues.Values m) (own opposing : ℚ)
    (unnormalized : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T (prepare m k).K))
    (anchorSpace : Fin m → (count : ℕ) → count≤(prepare m k).K → ℕ)
    (h : AtBound model W k limit b reciprocal prep inputs state resident parent columns values own opposing unnormalized anchorSpace) :
    ∀ j count hc,resident+parent+anchorSpace j count hc≤limit := by
  obtain ⟨D,F,hOld,hAnchor,hSum⟩ := h
  have hPrevious := GeneralPaperSourceDictionaryNormalizationStorage.retained_normalization model W k D b reciprocal prep inputs state resident parent columns values own opposing unnormalized hOld
    0 (by omega) 0 (by omega) none
  intro j count hc
  have ha := hAnchor j count hc
  omega

theorem source_stage {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv)
    (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool)
    (hModify : (GeneralPaperProxyClassifier.classify m k b).choice.modify≠none)
    (hGuard : ¬(reciprocal=true ∧ (GeneralPaperProxyClassifier.classify m k b).choice.endpoint=0))
    (hW : 1≤W) (hK : binaryWordWidth ((prepare m k).K+1)≤W) (hM : binaryWordWidth (m+1)≤W)
    (hIndex : binaryWordWidth ((prepare m k).S+2)≤W) (hDim : binaryWordWidth (m*((prepare m k).K-1)+3)≤W)
    (hBatch : binaryWordWidth (((prepare m k).S+1)*((prepare m k).K*(prepare m k).K)+3)≤W)
    (hFinalIndex : binaryWordWidth ((prepare m k).S+4)≤W) :
    let prep := GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b reciprocal
    let v := GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs
    let f := (GeneralPaperProxyClassifier.classify m k b).choice.proxy
    let inputs := GeneralPaperSharedBasisInputs.prepare k prep v f.num f.den reciprocal
    ∀ state,Invariant prep.dictionary v (prepare m k).S prep.threshold inputs.controls.N inputs.betaN inputs.initialGrid le_rfl state →
      AtBound model W k (GeneralPaperSourceQuantizedAnchorStorageRates.reservation model W m k Qv) b reciprocal prep inputs state
        (GeneralPaperSourceEnclosingOwners.window model W k Qv hQv weights hp hs b reciprocal)
        (GeneralPaperSourceStrictConstructorStorage.parentWindow model W k Qv hQv weights hp hs b reciprocal)
        (GeneralPaperSourceEnclosingOwners.columns model W k Qv weights b reciprocal)
        (GeneralPaperRetainedFieldValues.run true model W Qv hQv weights hp hs).1
        (GeneralPaperInitializerPreparedPoint.ownBudget m k b reciprocal) (GeneralPaperInitializerPreparedPoint.opposingBudget m k b reciprocal)
        (GeneralPaperSourceDictionaryNormalizationStorage.quantized model W k Qv weights b reciprocal)
        (window model W k Qv weights b reciprocal) := by
  dsimp only
  intro state inv
  have hOld := GeneralPaperSourceDictionaryNormalizationStorage.source_stage model W k Qv hm hQv weights hp hs b hb reciprocal hModify hGuard
    hW hK hM hIndex hDim hBatch hFinalIndex state inv
  exact ⟨GeneralPaperSourceDictionaryNormalizationStorageRates.reservation model W m k Qv,
    GeneralPaperSourceQuantizedAnchorStorageRates.sourceProfile model W m k,hOld,
    (source_anchors model W k Qv weights b reciprocal hW hK).1,le_rfl⟩

theorem actual_reached {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv)
    (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool)
    (hModify : (GeneralPaperProxyClassifier.classify m k b).choice.modify≠none)
    (hGuard : ¬(reciprocal=true ∧ (GeneralPaperProxyClassifier.classify m k b).choice.endpoint=0))
    (hW : 1≤W) (hK : binaryWordWidth ((prepare m k).K+1)≤W) (hM : binaryWordWidth (m+1)≤W)
    (hIndex : binaryWordWidth ((prepare m k).S+2)≤W) (hDim : binaryWordWidth (m*((prepare m k).K-1)+3)≤W)
    (hBatch : binaryWordWidth (((prepare m k).S+1)*((prepare m k).K*(prepare m k).K)+3)≤W)
    (hFinalIndex : binaryWordWidth ((prepare m k).S+4)≤W) :
    let prep := GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b reciprocal
    let v := GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs
    let f := (GeneralPaperProxyClassifier.classify m k b).choice.proxy
    let inputs := GeneralPaperSharedBasisInputs.prepare k prep v f.num f.den reciprocal
    ∃ state,(GeneralPaperBasisControllerBits.stages model W prep.dictionary.label inputs.matrix (prepare m k).S prep.threshold
      inputs.controls.N inputs.betaN inputs.initialGrid (m*((prepare m k).K-1)) le_rfl).1=some state ∧
      AtBound model W k (GeneralPaperSourceQuantizedAnchorStorageRates.reservation model W m k Qv) b reciprocal prep inputs state
        (GeneralPaperSourceEnclosingOwners.window model W k Qv hQv weights hp hs b reciprocal)
        (GeneralPaperSourceStrictConstructorStorage.parentWindow model W k Qv hQv weights hp hs b reciprocal)
        (GeneralPaperSourceEnclosingOwners.columns model W k Qv weights b reciprocal)
        (GeneralPaperRetainedFieldValues.run true model W Qv hQv weights hp hs).1
        (GeneralPaperInitializerPreparedPoint.ownBudget m k b reciprocal) (GeneralPaperInitializerPreparedPoint.opposingBudget m k b reciprocal)
        (GeneralPaperSourceDictionaryNormalizationStorage.quantized model W k Qv weights b reciprocal)
        (window model W k Qv weights b reciprocal) := by
  obtain ⟨state,hr,hOld⟩ := GeneralPaperSourceDictionaryNormalizationStorage.actual_reached model W k Qv hm hQv weights hp hs b hb reciprocal hModify hGuard
    hW hK hM hIndex hDim hBatch hFinalIndex
  exact ⟨state,hr,GeneralPaperSourceDictionaryNormalizationStorageRates.reservation model W m k Qv,
    GeneralPaperSourceQuantizedAnchorStorageRates.sourceProfile model W m k,hOld,
    (source_anchors model W k Qv weights b reciprocal hW hK).1,le_rfl⟩

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
      GeneralPaperSourceQuantizedAnchorStorageRates.sourceProfile model W m k≤
        GeneralPaperSourceQuantizedAnchorStorageRates.reservation model W m k Qv := by
  have hOld := GeneralPaperSourceDictionaryNormalizationStorage.guard_stage model W k Qv _hm hQv weights hp hs b hb reciprocal hModify hGuard hW hK hM hIndex
  exact Nat.add_le_add_right hOld _

end Blotto.GeneralPaperSourceQuantizedAnchorStorage
