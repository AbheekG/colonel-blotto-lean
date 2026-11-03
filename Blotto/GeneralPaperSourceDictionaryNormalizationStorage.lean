import Blotto.GeneralPaperSourceDictionaryNormalizationStorageRates
import Blotto.GeneralPaperRetainedSourceColumnBits

/-! Actual native source normalization. Original quantized rows,
proxy-budget and source height facts derive every nested anchor/payload,
reciprocal/multiply and work bound. The returned normalized columns are
exactly those retained by the existing source/endpoint proof chain. -/
namespace Blotto.GeneralPaperSourceDictionaryNormalizationStorage
open RationalOrderCell GeneralPaperProxyParameters GeneralPaperBasisStoredProducts
open GeneralPaperBasisState GeneralPaperBasisInvariant GeneralPaperEncodedScalarStorage
open GeneralPaperEncodedBasisStorage (integerBits arrayFootprint arrayProfile)
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 18000000
set_option maxRecDepth 16384

noncomputable def quantized {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (weights : FixedArrayTable m ℕ)
    (b : ℝ) (reciprocal : Bool) :=
  (GeneralPaperNativeDivisibleColumns.run model.rat (fun w => w) W
    (GeneralPaperTrajectoryParameters.rows_positive (alphabet m k).lambda k) (GeneralPaperScoreScaleParameters.labels_positive m k)
    (GeneralPaperTrajectoryParameters.labels_divide_rows m (alphabet m k).lambda k)
    (GeneralPaperSourceInitializer.sourceRows k Qv weights b reciprocal)).1

noncomputable def window {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (weights : FixedArrayTable m ℕ)
    (b : ℝ) (reciprocal : Bool) (outer : ℕ) (ho : outer≤m) (inner : ℕ) (hi : inner≤(prepare m k).K) (active : Option (Fin m)) : ℕ :=
  GeneralPaperDictionaryNormalizationStorage.window model W (GeneralPaperInitializerPreparedPoint.ownBudget m k b reciprocal)
    (quantized model W k Qv weights b reciprocal) outer ho inner hi active

def NormalizationBound {T m : ℕ} (model : RationalCostModel) (W k limit : ℕ) (budget : ℚ)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T (prepare m k).K)) : Prop :=
  ∀ outer (ho : outer≤m) inner (hi : inner≤(prepare m k).K) active,
    GeneralPaperDictionaryNormalizationStorage.window model W budget columns outer ho inner hi active≤limit

theorem normalization_mono {T m : ℕ} (model : RationalCostModel) (W k B C : ℕ) (budget : ℚ)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T (prepare m k).K)) (hBC : B≤C)
    (h : NormalizationBound model W k B budget columns) : NormalizationBound model W k C budget columns :=
  fun outer ho inner hi active => (h outer ho inner hi active).trans hBC

theorem native_columns {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (weights : FixedArrayTable m ℕ) (b : ℝ) (reciprocal : Bool) :
    (GeneralPaperNativeDictionaryNormalize.run model.rat (fun w => w) W (GeneralPaperInitializerPreparedPoint.ownBudget m k b reciprocal)
      (quantized model W k Qv weights b reciprocal)).1=GeneralPaperSourceEnclosingOwners.columns model W k Qv weights b reciprocal := rfl

theorem source_normalization {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (weights : FixedArrayTable m ℕ)
    (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool) (hW : 1≤W)
    (hK : binaryWordWidth ((prepare m k).K+1)≤W) (hM : binaryWordWidth (m+1)≤W) :
    NormalizationBound model W k (GeneralPaperSourceDictionaryNormalizationStorageRates.sourceProfile model W m k)
      (GeneralPaperInitializerPreparedPoint.ownBudget m k b reciprocal) (quantized model W k Qv weights b reciprocal) ∧
      (GeneralPaperNativeDictionaryNormalize.run model.rat (fun w => w) W (GeneralPaperInitializerPreparedPoint.ownBudget m k b reciprocal)
        (quantized model W k Qv weights b reciprocal)).2≤GeneralPaperDictionaryNormalizationStorage.price model W m (prepare m k).K
          (GeneralPaperSourceDictionaryNormalizationStorageRates.operandWidth m k) := by
  let old := quantized model W k Qv weights b reciprocal
  let budget := GeneralPaperInitializerPreparedPoint.ownBudget m k b reciprocal
  let R := GeneralPaperSourceDictionaryNormalizationStorageRates.operandWidth m k
  have hBudget := GeneralPaperSourceScoreHeights.own_height m k b hb reciprocal
  have hOld (j l) : RationalHeight ((old.read j).anchors.read l) (binaryWordWidth (alphabet m k).C) :=
    GeneralPaperNativeUnitSourceJoin.quantized_height model.rat (fun w => w) W
      (GeneralPaperTrajectoryParameters.rows_positive (alphabet m k).lambda k) (GeneralPaperScoreScaleParameters.labels_positive m k)
      (GeneralPaperTrajectoryParameters.labels_divide_rows m (alphabet m k).lambda k)
      (GeneralPaperSourceInitializer.sourceRows k Qv weights b reciprocal) _
      (GeneralPaperSourceScoreHeights.rows_height k Qv weights b reciprocal) j l
  have hB : rationalWordWidth budget≤R := by
    have h := rationalWordWidth_of_height hBudget
    unfold R GeneralPaperSourceDictionaryNormalizationStorageRates.operandWidth GeneralPaperSourceScoreHeights.anchorHeight
    change rationalWordWidth budget≤_ at h
    omega
  have hC : rationalWordWidth budget⁻¹≤R := by
    have h := rationalWordWidth_of_height hBudget.inv
    unfold R GeneralPaperSourceDictionaryNormalizationStorageRates.operandWidth GeneralPaperSourceScoreHeights.anchorHeight
    change rationalWordWidth budget⁻¹≤_ at h
    omega
  have hX (j l) : rationalWordWidth ((old.read j).anchors.read l)≤R := by
    have h := rationalWordWidth_of_height (hOld j l)
    unfold R GeneralPaperSourceDictionaryNormalizationStorageRates.operandWidth GeneralPaperSourceScoreHeights.anchorHeight
    omega
  have hP (j l) : rationalWordWidth (budget⁻¹*(old.read j).anchors.read l)≤R := by
    have h := rationalWordWidth_of_height (hBudget.inv.mul (hOld j l))
    change rationalWordWidth (budget⁻¹*(old.read j).anchors.read l)≤_ at h
    unfold R GeneralPaperSourceDictionaryNormalizationStorageRates.operandWidth GeneralPaperSourceScoreHeights.anchorHeight
    omega
  refine ⟨?_,GeneralPaperDictionaryNormalizationStorage.work model W R budget old hB hC hX hP hW hK hM⟩
  intro outer ho inner hi active
  exact GeneralPaperDictionaryNormalizationStorage.bounded model W R budget old hB hC hX hP hW hK hM outer ho inner hi active

def AtBound {T m : ℕ} (model : RationalCostModel) (W k limit : ℕ) (b : ℝ) (reciprocal : Bool)
    (prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K)
    (state : State (m*((prepare m k).K-1)) (m*((prepare m k).K-1))) (resident parent : ℕ)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T (prepare m k).K))
    (values : GeneralPaperRetainedFieldValues.Values m) (own opposing : ℚ)
    (unnormalized : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T (prepare m k).K)) : Prop :=
  ∃ D N,GeneralPaperSourceStrictChildStorage.AtBound model W k D b reciprocal prep inputs state resident parent columns values own opposing ∧
    NormalizationBound model W k N own unnormalized ∧ D+N≤limit

theorem bound_mono {T m : ℕ} (model : RationalCostModel) (W k : ℕ) (b : ℝ) (reciprocal : Bool)
    (prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K)
    (state : State (m*((prepare m k).K-1)) (m*((prepare m k).K-1))) (resident parent : ℕ)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T (prepare m k).K))
    (values : GeneralPaperRetainedFieldValues.Values m) (own opposing : ℚ) (unnormalized : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T (prepare m k).K)) (B C : ℕ) (hBC : B≤C)
    (h : AtBound model W k B b reciprocal prep inputs state resident parent columns values own opposing unnormalized) :
    AtBound model W k C b reciprocal prep inputs state resident parent columns values own opposing unnormalized := by
  obtain ⟨D,N,hOld,hNormalization,hSum⟩ := h
  exact ⟨D,N,hOld,hNormalization,hSum.trans hBC⟩

theorem retained_normalization {T m : ℕ} (model : RationalCostModel) (W k limit : ℕ) (b : ℝ) (reciprocal : Bool)
    (prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K)
    (state : State (m*((prepare m k).K-1)) (m*((prepare m k).K-1))) (resident parent : ℕ)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T (prepare m k).K))
    (values : GeneralPaperRetainedFieldValues.Values m) (own opposing : ℚ)
    (unnormalized : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T (prepare m k).K))
    (h : AtBound model W k limit b reciprocal prep inputs state resident parent columns values own opposing unnormalized) :
    ∀ outer (ho : outer≤m) inner (hi : inner≤(prepare m k).K) active,
      resident+parent+GeneralPaperDictionaryNormalizationStorage.window model W own unnormalized outer ho inner hi active≤limit := by
  obtain ⟨D,N,hOld,hNorm,hSum⟩ := h
  have hPrevious := GeneralPaperSourceStrictChildStorage.retained_children model W k D b reciprocal prep inputs state resident parent columns values own opposing hOld
    0 (by omega) 0 (by omega) 0 (by omega)
  intro outer ho inner hi active
  have hn := hNorm outer ho inner hi active
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
      AtBound model W k (GeneralPaperSourceDictionaryNormalizationStorageRates.reservation model W m k Qv) b reciprocal prep inputs state
        (GeneralPaperSourceEnclosingOwners.window model W k Qv hQv weights hp hs b reciprocal)
        (GeneralPaperSourceStrictConstructorStorage.parentWindow model W k Qv hQv weights hp hs b reciprocal)
        (GeneralPaperSourceEnclosingOwners.columns model W k Qv weights b reciprocal)
        (GeneralPaperRetainedFieldValues.run true model W Qv hQv weights hp hs).1
        (GeneralPaperInitializerPreparedPoint.ownBudget m k b reciprocal) (GeneralPaperInitializerPreparedPoint.opposingBudget m k b reciprocal)
        (quantized model W k Qv weights b reciprocal) := by
  dsimp only
  intro state inv
  have hOld := GeneralPaperSourceStrictChildStorage.source_stage model W k Qv hm hQv weights hp hs b hb reciprocal hModify hGuard
    hW hK hM hIndex hDim hBatch hFinalIndex state inv
  exact ⟨GeneralPaperSourceStrictChildStorageRates.reservation model W m k Qv,
    GeneralPaperSourceDictionaryNormalizationStorageRates.sourceProfile model W m k,hOld,
    (source_normalization model W k Qv weights b hb reciprocal hW hK hM).1,le_rfl⟩

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
      AtBound model W k (GeneralPaperSourceDictionaryNormalizationStorageRates.reservation model W m k Qv) b reciprocal prep inputs state
        (GeneralPaperSourceEnclosingOwners.window model W k Qv hQv weights hp hs b reciprocal)
        (GeneralPaperSourceStrictConstructorStorage.parentWindow model W k Qv hQv weights hp hs b reciprocal)
        (GeneralPaperSourceEnclosingOwners.columns model W k Qv weights b reciprocal)
        (GeneralPaperRetainedFieldValues.run true model W Qv hQv weights hp hs).1
        (GeneralPaperInitializerPreparedPoint.ownBudget m k b reciprocal) (GeneralPaperInitializerPreparedPoint.opposingBudget m k b reciprocal)
        (quantized model W k Qv weights b reciprocal) := by
  obtain ⟨state,hr,hOld⟩ := GeneralPaperSourceStrictChildStorage.actual_reached model W k Qv hm hQv weights hp hs b hb reciprocal hModify hGuard
    hW hK hM hIndex hDim hBatch hFinalIndex
  exact ⟨state,hr,GeneralPaperSourceStrictChildStorageRates.reservation model W m k Qv,
    GeneralPaperSourceDictionaryNormalizationStorageRates.sourceProfile model W m k,hOld,
    (source_normalization model W k Qv weights b hb reciprocal hW hK hM).1,le_rfl⟩

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
      GeneralPaperSourceDictionaryNormalizationStorageRates.sourceProfile model W m k≤
        GeneralPaperSourceDictionaryNormalizationStorageRates.reservation model W m k Qv := by
  have hOld := GeneralPaperSourceStrictChildStorage.guard_stage model W k Qv _hm hQv weights hp hs b hb reciprocal hModify hGuard hW hK hM hIndex
  exact Nat.add_le_add_right hOld _

end Blotto.GeneralPaperSourceDictionaryNormalizationStorage
