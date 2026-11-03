import Blotto.GeneralPaperSourceRepresentativeSortStorageRates
import Blotto.GeneralPaperRetainedSourceColumnBits

/-! Actual representative sort on the original materialized source
column. The stored original-index permutation is shared with the native
anchor/label constructors; all arbitrary packing/comparison windows SUM
with the complete previously checked source and endpoint reservation. -/
namespace Blotto.GeneralPaperSourceRepresentativeSortStorage
open RationalOrderCell GeneralPaperProxyParameters GeneralPaperBasisStoredProducts
open GeneralPaperBasisState GeneralPaperBasisInvariant GeneralPaperEncodedScalarStorage
open GeneralPaperEncodedBasisStorage (integerBits arrayFootprint arrayProfile)
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 18000000
set_option maxRecDepth 16384

abbrev Active (model : RationalCostModel) (W m k : ℕ) :=
  Option (Fin ((prepare m k).K*GeneralPaperSourceQuantizedAnchorStorage.blockSize model W m k) ×
    Fin ((prepare m k).K*GeneralPaperSourceQuantizedAnchorStorage.blockSize model W m k))

noncomputable def window {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (weights : FixedArrayTable m ℕ)
    (b : ℝ) (reciprocal : Bool) (j : Fin m) (used copied : ℕ) (active : Active model W m k) : ℕ :=
  GeneralPaperRepresentativeSortStorage.window model W
    (GeneralPaperSourceQuantizedAnchorStorage.values model W k Qv weights b reciprocal j) used copied active

theorem native_order {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (weights : FixedArrayTable m ℕ)
    (b : ℝ) (reciprocal : Bool) (j : Fin m) :
    (GeneralPaperNativeRepresentativeSort.run model.rat (fun w => w) W
      (GeneralPaperSourceQuantizedAnchorStorage.values model W k Qv weights b reciprocal j)).1=
        GeneralPaperSourceQuantizedAnchorStorage.order model W k Qv weights b reciprocal j := rfl

theorem order_data {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (weights : FixedArrayTable m ℕ)
    (b : ℝ) (reciprocal : Bool) (j : Fin m) :
    GeneralPaperSourceQuantizedAnchorStorage.order model W k Qv weights b reciprocal j=
      GeneralPaperRowSort.order (GeneralPaperSourceQuantizedAnchorStorage.values model W k Qv weights b reciprocal j) :=
  GeneralPaperNativeRepresentativeSort.data model.rat (fun w => w) W _

theorem source_values {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (weights : FixedArrayTable m ℕ)
    (b : ℝ) (reciprocal : Bool) :
    ∀ j i,rationalWordWidth ((GeneralPaperSourceQuantizedAnchorStorage.values model W k Qv weights b reciprocal j).read i)≤
      GeneralPaperSourceRepresentativeSortStorageRates.operandWidth m k := by
  let R := GeneralPaperSourceRepresentativeSortStorageRates.operandWidth m k
  have hRows (i l) : rationalWordWidth (((GeneralPaperSourceInitializer.sourceRows k Qv weights b reciprocal).read i).read l)≤R := by
    have h := rationalWordWidth_of_height (GeneralPaperSourceScoreHeights.rows_height k Qv weights b reciprocal i l)
    unfold R GeneralPaperSourceRepresentativeSortStorageRates.operandWidth GeneralPaperSourceScoreHeights.anchorHeight
    omega
  intro j i
  unfold GeneralPaperSourceQuantizedAnchorStorage.values
  rw [GeneralPaperNativeQuantizedMatrix.input_data,GeneralPaperRowQuantizer.columnInput,FixedArrayTable.read_ofFn]
  exact GeneralPaperNativeDivisibleColumns.cast_words (GeneralPaperSourceQuantizedAnchorStorage.size_eq model W m k) _ R hRows i j

theorem source_sort {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (weights : FixedArrayTable m ℕ)
    (b : ℝ) (reciprocal : Bool) (hW : 1≤W)
    (hT : binaryWordWidth ((GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows+1)≤W) :
    (∀ j used copied active,window model W k Qv weights b reciprocal j used copied active≤
      GeneralPaperSourceRepresentativeSortStorageRates.sourceProfile model W m k) ∧
      ∀ j,(GeneralPaperNativeRepresentativeSort.run model.rat (fun w => w) W
        (GeneralPaperSourceQuantizedAnchorStorage.values model W k Qv weights b reciprocal j)).2≤
          GeneralPaperRepresentativeSortStorage.price model W
            (GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows
            (GeneralPaperSourceRepresentativeSortStorageRates.operandWidth m k) := by
  let R := GeneralPaperSourceRepresentativeSortStorageRates.operandWidth m k
  have hIndex : binaryWordWidth ((prepare m k).K*GeneralPaperSourceQuantizedAnchorStorage.blockSize model W m k+1)≤W := by
    rw [←GeneralPaperSourceQuantizedAnchorStorage.size_eq model W m k]
    exact hT
  have hValues := source_values model W k Qv weights b reciprocal
  refine ⟨?_,?_⟩
  · intro j used copied active
    have h := GeneralPaperRepresentativeSortStorage.bounded model W R
      (GeneralPaperSourceQuantizedAnchorStorage.values model W k Qv weights b reciprocal j) (hValues j) hW hIndex used copied active
    apply h.trans
    rw [←GeneralPaperSourceQuantizedAnchorStorage.size_eq model W m k]
    exact Nat.le_refl _
  · intro j
    have h := GeneralPaperRepresentativeSortStorage.work model W R
      (GeneralPaperSourceQuantizedAnchorStorage.values model W k Qv weights b reciprocal j) (hValues j) hW hIndex
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
    (sortSpace : Fin m → ℕ → ℕ → Active model W m k → ℕ) : Prop :=
  ∃ D F,GeneralPaperSourceQuantizedAnchorStorage.AtBound model W k D b reciprocal prep inputs state resident parent columns values own opposing unnormalized anchorSpace ∧
    (∀ j used copied active,sortSpace j used copied active≤F) ∧ D+F≤limit

theorem bound_mono {T m : ℕ} (model : RationalCostModel) (W k : ℕ) (b : ℝ) (reciprocal : Bool)
    (prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K)
    (state : State (m*((prepare m k).K-1)) (m*((prepare m k).K-1))) (resident parent : ℕ)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T (prepare m k).K))
    (values : GeneralPaperRetainedFieldValues.Values m) (own opposing : ℚ) (unnormalized : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T (prepare m k).K)) (anchorSpace : Fin m → (count : ℕ) → count≤(prepare m k).K → ℕ) (sortSpace : Fin m → ℕ → ℕ → Active model W m k → ℕ) (B C : ℕ) (hBC : B≤C)
    (h : AtBound model W k B b reciprocal prep inputs state resident parent columns values own opposing unnormalized anchorSpace sortSpace) :
    AtBound model W k C b reciprocal prep inputs state resident parent columns values own opposing unnormalized anchorSpace sortSpace := by
  obtain ⟨D,F,hOld,hSort,hSum⟩ := h
  exact ⟨D,F,hOld,hSort,hSum.trans hBC⟩

theorem retained_sort {T m : ℕ} (model : RationalCostModel) (W k limit : ℕ) (b : ℝ) (reciprocal : Bool)
    (prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K)
    (state : State (m*((prepare m k).K-1)) (m*((prepare m k).K-1))) (resident parent : ℕ)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T (prepare m k).K))
    (values : GeneralPaperRetainedFieldValues.Values m) (own opposing : ℚ)
    (unnormalized : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T (prepare m k).K))
    (anchorSpace : Fin m → (count : ℕ) → count≤(prepare m k).K → ℕ)
    (sortSpace : Fin m → ℕ → ℕ → Active model W m k → ℕ)
    (h : AtBound model W k limit b reciprocal prep inputs state resident parent columns values own opposing unnormalized anchorSpace sortSpace) :
    ∀ j count hc l used copied active,resident+parent+anchorSpace j count hc+sortSpace l used copied active≤limit := by
  obtain ⟨D,F,hOld,hSort,hSum⟩ := h
  have hPrevious := GeneralPaperSourceQuantizedAnchorStorage.retained_anchors model W k D b reciprocal prep inputs state resident parent columns values own opposing unnormalized anchorSpace hOld
  intro j count hc l used copied active
  have hp := hPrevious j count hc
  have hs := hSort l used copied active
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
      AtBound model W k (GeneralPaperSourceRepresentativeSortStorageRates.reservation model W m k Qv) b reciprocal prep inputs state
        (GeneralPaperSourceEnclosingOwners.window model W k Qv hQv weights hp hs b reciprocal)
        (GeneralPaperSourceStrictConstructorStorage.parentWindow model W k Qv hQv weights hp hs b reciprocal)
        (GeneralPaperSourceEnclosingOwners.columns model W k Qv weights b reciprocal)
        (GeneralPaperRetainedFieldValues.run true model W Qv hQv weights hp hs).1
        (GeneralPaperInitializerPreparedPoint.ownBudget m k b reciprocal) (GeneralPaperInitializerPreparedPoint.opposingBudget m k b reciprocal)
        (GeneralPaperSourceDictionaryNormalizationStorage.quantized model W k Qv weights b reciprocal)
        (GeneralPaperSourceQuantizedAnchorStorage.window model W k Qv weights b reciprocal)
        (window model W k Qv weights b reciprocal) := by
  dsimp only
  intro state inv
  have hOld := GeneralPaperSourceQuantizedAnchorStorage.source_stage model W k Qv hm hQv weights hp hs b hb reciprocal hModify hGuard
    hW hK hM hIndex hDim hBatch hFinalIndex state inv
  exact ⟨GeneralPaperSourceQuantizedAnchorStorageRates.reservation model W m k Qv,
    GeneralPaperSourceRepresentativeSortStorageRates.sourceProfile model W m k,hOld,
    (source_sort model W k Qv weights b reciprocal hW hT).1,le_rfl⟩

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
      AtBound model W k (GeneralPaperSourceRepresentativeSortStorageRates.reservation model W m k Qv) b reciprocal prep inputs state
        (GeneralPaperSourceEnclosingOwners.window model W k Qv hQv weights hp hs b reciprocal)
        (GeneralPaperSourceStrictConstructorStorage.parentWindow model W k Qv hQv weights hp hs b reciprocal)
        (GeneralPaperSourceEnclosingOwners.columns model W k Qv weights b reciprocal)
        (GeneralPaperRetainedFieldValues.run true model W Qv hQv weights hp hs).1
        (GeneralPaperInitializerPreparedPoint.ownBudget m k b reciprocal) (GeneralPaperInitializerPreparedPoint.opposingBudget m k b reciprocal)
        (GeneralPaperSourceDictionaryNormalizationStorage.quantized model W k Qv weights b reciprocal)
        (GeneralPaperSourceQuantizedAnchorStorage.window model W k Qv weights b reciprocal)
        (window model W k Qv weights b reciprocal) := by
  obtain ⟨state,hr,hOld⟩ := GeneralPaperSourceQuantizedAnchorStorage.actual_reached model W k Qv hm hQv weights hp hs b hb reciprocal hModify hGuard
    hW hK hM hIndex hDim hBatch hFinalIndex
  exact ⟨state,hr,GeneralPaperSourceQuantizedAnchorStorageRates.reservation model W m k Qv,
    GeneralPaperSourceRepresentativeSortStorageRates.sourceProfile model W m k,hOld,
    (source_sort model W k Qv weights b reciprocal hW hT).1,le_rfl⟩

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
      GeneralPaperSourceRepresentativeSortStorageRates.sourceProfile model W m k≤
        GeneralPaperSourceRepresentativeSortStorageRates.reservation model W m k Qv := by
  have hOld := GeneralPaperSourceQuantizedAnchorStorage.guard_stage model W k Qv _hm hQv weights hp hs b hb reciprocal hModify hGuard hW hK hM hIndex
  exact Nat.add_le_add_right hOld _

end Blotto.GeneralPaperSourceRepresentativeSortStorage
