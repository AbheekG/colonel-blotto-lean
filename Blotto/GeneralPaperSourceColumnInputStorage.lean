import Blotto.GeneralPaperSourceColumnInputStorageRates
import Blotto.GeneralPaperRetainedSourceColumnBits

/-! Literal source-column materialization on the same retained rows
used by the native quantizer, representative sort and anchor constructor.
Full matrix/row/value and fill owners SUM with all preceding contracts;
source-row heights derive all payloads without acceptance/basis premises. -/
namespace Blotto.GeneralPaperSourceColumnInputStorage
open RationalOrderCell GeneralPaperProxyParameters GeneralPaperBasisStoredProducts
open GeneralPaperBasisState GeneralPaperBasisInvariant GeneralPaperEncodedScalarStorage
open GeneralPaperEncodedBasisStorage (integerBits arrayFootprint arrayProfile)
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 18000000
set_option maxRecDepth 16384

noncomputable def rows {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (weights : FixedArrayTable m ℕ)
    (b : ℝ) (reciprocal : Bool) :=
  GeneralPaperRowQuantizer.castRows (GeneralPaperSourceQuantizedAnchorStorage.size_eq model W m k)
    (GeneralPaperSourceInitializer.sourceRows k Qv weights b reciprocal)

noncomputable def window {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (weights : FixedArrayTable m ℕ)
    (b : ℝ) (reciprocal : Bool) (j : Fin m) (count : ℕ)
    (hc : count≤(GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows) : ℕ :=
  GeneralPaperColumnInputStorage.window W (rows model W k Qv weights b reciprocal) j count
    (by rw [←GeneralPaperSourceQuantizedAnchorStorage.size_eq model W m k];exact hc)

theorem native_input {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (weights : FixedArrayTable m ℕ)
    (b : ℝ) (reciprocal : Bool) (j : Fin m) :
    (GeneralPaperNativeQuantizedMatrix.columnInput (fun w => w) W (rows model W k Qv weights b reciprocal) j).1=
      GeneralPaperSourceQuantizedAnchorStorage.values model W k Qv weights b reciprocal j := rfl

theorem rows_owner {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (weights : FixedArrayTable m ℕ)
    (b : ℝ) (reciprocal : Bool) :
    GeneralPaperEnclosingSourceOwners.rowsFoot W (rows model W k Qv weights b reciprocal)=
      GeneralPaperEnclosingSourceOwners.rowsFoot W (GeneralPaperSourceInitializer.sourceRows k Qv weights b reciprocal) :=
  GeneralPaperColumnInputStorage.cast_rows_foot W (GeneralPaperSourceQuantizedAnchorStorage.size_eq model W m k) _

theorem source_rows {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (weights : FixedArrayTable m ℕ)
    (b : ℝ) (reciprocal : Bool) :
    ∀ i j,rationalWordWidth (((rows model W k Qv weights b reciprocal).read i).read j)≤
      GeneralPaperSourceColumnInputStorageRates.operandWidth m k := by
  apply GeneralPaperNativeDivisibleColumns.cast_words
  intro i j
  have h := rationalWordWidth_of_height (GeneralPaperSourceScoreHeights.rows_height k Qv weights b reciprocal i j)
  unfold GeneralPaperSourceColumnInputStorageRates.operandWidth GeneralPaperSourceScoreHeights.anchorHeight
  omega

theorem source_materialization {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (weights : FixedArrayTable m ℕ)
    (b : ℝ) (reciprocal : Bool) (hW : 1≤W)
    (hT : binaryWordWidth ((GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows+1)≤W) :
    (∀ j count hc,window model W k Qv weights b reciprocal j count hc≤
      GeneralPaperSourceColumnInputStorageRates.sourceProfile model W m k) ∧
      ∀ j,(GeneralPaperNativeQuantizedMatrix.columnInput (fun w => w) W
        (rows model W k Qv weights b reciprocal) j).2≤
          GeneralPaperColumnInputStorage.price W (GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows := by
  let R := GeneralPaperSourceColumnInputStorageRates.operandWidth m k
  have hIndex : binaryWordWidth ((prepare m k).K*GeneralPaperSourceQuantizedAnchorStorage.blockSize model W m k+1)≤W := by
    rw [←GeneralPaperSourceQuantizedAnchorStorage.size_eq model W m k]
    exact hT
  have hRows := source_rows model W k Qv weights b reciprocal
  refine ⟨?_,?_⟩
  · intro j count hc
    have h := GeneralPaperColumnInputStorage.bounded W R (rows model W k Qv weights b reciprocal) hRows hW hIndex j count
      (by rw [←GeneralPaperSourceQuantizedAnchorStorage.size_eq model W m k];exact hc)
    apply h.trans
    rw [←GeneralPaperSourceQuantizedAnchorStorage.size_eq model W m k]
    exact Nat.le_refl _
  · intro j
    have h := GeneralPaperColumnInputStorage.work W (rows model W k Qv weights b reciprocal) j hW hIndex
    apply h.trans
    rw [←GeneralPaperSourceQuantizedAnchorStorage.size_eq model W m k]

def AtBound {T m : ℕ} (model : RationalCostModel) (W k limit : ℕ) (b : ℝ) (reciprocal : Bool)
    (prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K)
    (state : State (m*((prepare m k).K-1)) (m*((prepare m k).K-1))) (resident parent : ℕ)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T (prepare m k).K))
    (values : GeneralPaperRetainedFieldValues.Values m) (own opposing : ℚ)
    (unnormalized : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T (prepare m k).K))
    (anchorSpace : Fin m → (count : ℕ) → count≤(prepare m k).K → ℕ)
    (sortSpace : Fin m → ℕ → ℕ → GeneralPaperSourceRepresentativeSortStorage.Active model W m k → ℕ)
    (materialSpace : Fin m → (count : ℕ) → count≤(GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows → ℕ) : Prop :=
  ∃ D F,GeneralPaperSourceRepresentativeSortStorage.AtBound model W k D b reciprocal prep inputs state resident parent columns values own opposing unnormalized anchorSpace sortSpace ∧
    (∀ j count hc,materialSpace j count hc≤F) ∧ D+F≤limit

theorem bound_mono {T m : ℕ} (model : RationalCostModel) (W k : ℕ) (b : ℝ) (reciprocal : Bool)
    (prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K)
    (state : State (m*((prepare m k).K-1)) (m*((prepare m k).K-1))) (resident parent : ℕ)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T (prepare m k).K))
    (values : GeneralPaperRetainedFieldValues.Values m) (own opposing : ℚ) (unnormalized : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T (prepare m k).K)) (anchorSpace : Fin m → (count : ℕ) → count≤(prepare m k).K → ℕ) (sortSpace : Fin m → ℕ → ℕ → GeneralPaperSourceRepresentativeSortStorage.Active model W m k → ℕ) (materialSpace : Fin m → (count : ℕ) → count≤(GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows → ℕ) (B C : ℕ) (hBC : B≤C)
    (h : AtBound model W k B b reciprocal prep inputs state resident parent columns values own opposing unnormalized anchorSpace sortSpace materialSpace) :
    AtBound model W k C b reciprocal prep inputs state resident parent columns values own opposing unnormalized anchorSpace sortSpace materialSpace := by
  obtain ⟨D,F,hOld,hMaterial,hSum⟩ := h
  exact ⟨D,F,hOld,hMaterial,hSum.trans hBC⟩

theorem retained_materialization {T m : ℕ} (model : RationalCostModel) (W k limit : ℕ) (b : ℝ) (reciprocal : Bool)
    (prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K)
    (state : State (m*((prepare m k).K-1)) (m*((prepare m k).K-1))) (resident parent : ℕ)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T (prepare m k).K))
    (values : GeneralPaperRetainedFieldValues.Values m) (own opposing : ℚ)
    (unnormalized : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T (prepare m k).K))
    (anchorSpace : Fin m → (count : ℕ) → count≤(prepare m k).K → ℕ)
    (sortSpace : Fin m → ℕ → ℕ → GeneralPaperSourceRepresentativeSortStorage.Active model W m k → ℕ)
    (materialSpace : Fin m → (count : ℕ) → count≤(GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows → ℕ)
    (h : AtBound model W k limit b reciprocal prep inputs state resident parent columns values own opposing unnormalized anchorSpace sortSpace materialSpace) :
    ∀ j count hc l used copied active p fill hf,
      resident+parent+anchorSpace j count hc+sortSpace l used copied active+materialSpace p fill hf≤limit := by
  obtain ⟨D,F,hOld,hMaterial,hSum⟩ := h
  have hPrevious := GeneralPaperSourceRepresentativeSortStorage.retained_sort model W k D b reciprocal prep inputs state resident parent columns values own opposing unnormalized anchorSpace sortSpace hOld
  intro j count hc l used copied active p fill hf
  have hp := hPrevious j count hc l used copied active
  have hs := hMaterial p fill hf
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
      AtBound model W k (GeneralPaperSourceColumnInputStorageRates.reservation model W m k Qv) b reciprocal prep inputs state
        (GeneralPaperSourceEnclosingOwners.window model W k Qv hQv weights hp hs b reciprocal)
        (GeneralPaperSourceStrictConstructorStorage.parentWindow model W k Qv hQv weights hp hs b reciprocal)
        (GeneralPaperSourceEnclosingOwners.columns model W k Qv weights b reciprocal)
        (GeneralPaperRetainedFieldValues.run true model W Qv hQv weights hp hs).1
        (GeneralPaperInitializerPreparedPoint.ownBudget m k b reciprocal) (GeneralPaperInitializerPreparedPoint.opposingBudget m k b reciprocal)
        (GeneralPaperSourceDictionaryNormalizationStorage.quantized model W k Qv weights b reciprocal)
        (GeneralPaperSourceQuantizedAnchorStorage.window model W k Qv weights b reciprocal)
        (GeneralPaperSourceRepresentativeSortStorage.window model W k Qv weights b reciprocal)
        (window model W k Qv weights b reciprocal) := by
  dsimp only
  intro state inv
  have hOld := GeneralPaperSourceRepresentativeSortStorage.source_stage model W k Qv hm hQv weights hp hs b hb reciprocal hModify hGuard
    hW hK hM hIndex hDim hBatch hT hFinalIndex state inv
  exact ⟨GeneralPaperSourceRepresentativeSortStorageRates.reservation model W m k Qv,
    GeneralPaperSourceColumnInputStorageRates.sourceProfile model W m k,hOld,
    (source_materialization model W k Qv weights b reciprocal hW hT).1,le_rfl⟩

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
      AtBound model W k (GeneralPaperSourceColumnInputStorageRates.reservation model W m k Qv) b reciprocal prep inputs state
        (GeneralPaperSourceEnclosingOwners.window model W k Qv hQv weights hp hs b reciprocal)
        (GeneralPaperSourceStrictConstructorStorage.parentWindow model W k Qv hQv weights hp hs b reciprocal)
        (GeneralPaperSourceEnclosingOwners.columns model W k Qv weights b reciprocal)
        (GeneralPaperRetainedFieldValues.run true model W Qv hQv weights hp hs).1
        (GeneralPaperInitializerPreparedPoint.ownBudget m k b reciprocal) (GeneralPaperInitializerPreparedPoint.opposingBudget m k b reciprocal)
        (GeneralPaperSourceDictionaryNormalizationStorage.quantized model W k Qv weights b reciprocal)
        (GeneralPaperSourceQuantizedAnchorStorage.window model W k Qv weights b reciprocal)
        (GeneralPaperSourceRepresentativeSortStorage.window model W k Qv weights b reciprocal)
        (window model W k Qv weights b reciprocal) := by
  obtain ⟨state,hr,hOld⟩ := GeneralPaperSourceRepresentativeSortStorage.actual_reached model W k Qv hm hQv weights hp hs b hb reciprocal hModify hGuard
    hW hK hM hIndex hDim hBatch hT hFinalIndex
  exact ⟨state,hr,GeneralPaperSourceRepresentativeSortStorageRates.reservation model W m k Qv,
    GeneralPaperSourceColumnInputStorageRates.sourceProfile model W m k,hOld,
    (source_materialization model W k Qv weights b reciprocal hW hT).1,le_rfl⟩

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
      GeneralPaperSourceColumnInputStorageRates.sourceProfile model W m k≤
        GeneralPaperSourceColumnInputStorageRates.reservation model W m k Qv := by
  have hOld := GeneralPaperSourceRepresentativeSortStorage.guard_stage model W k Qv _hm hQv weights hp hs b hb reciprocal hModify hGuard hW hK hM hIndex
  exact Nat.add_le_add_right hOld _

end Blotto.GeneralPaperSourceColumnInputStorage
