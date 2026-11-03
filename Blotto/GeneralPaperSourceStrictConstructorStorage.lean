import Blotto.GeneralPaperSourceStrictConstructorStorageRates
import Blotto.GeneralPaperRetainedSourceColumnBits

/-! Literal strict-preparation parent and full active matrix/recursive
strict-score DP constructor windows SUM with complete preceding resident
source/endpoint owners. Every height and work premise comes from actual
native source data. Threshold/maximum child scans and remaining source/
column/pair constructors and global calibration remain separate joins. -/
namespace Blotto.GeneralPaperSourceStrictConstructorStorage
open RationalOrderCell GeneralPaperProxyParameters GeneralPaperBasisStoredProducts
open GeneralPaperBasisState GeneralPaperBasisInvariant GeneralPaperEncodedScalarStorage
open GeneralPaperEncodedBasisStorage (integerBits arrayFootprint arrayProfile)
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 18000000
set_option maxRecDepth 16384

noncomputable def parentWindow {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv) (b : ℝ) (reciprocal : Bool) : ℕ :=
  GeneralPaperRetainedStrictParentStorage.window model W (GeneralPaperScoreScaleParameters.prepare m k).depth (prepare m k).S
    (GeneralPaperScoreScaleParameters.labels_positive m k) (GeneralPaperSourceEnclosingOwners.columns model W k Qv weights b reciprocal)
    (GeneralPaperRetainedFieldValues.run true model W Qv hQv weights hp hs).1
    (GeneralPaperInitializerPreparedPoint.ownBudget m k b reciprocal) (GeneralPaperInitializerPreparedPoint.opposingBudget m k b reciprocal)

def MatrixBound {T m : ℕ} (model : RationalCostModel) (W k limit : ℕ)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T (prepare m k).K))
    (values : GeneralPaperRetainedFieldValues.Values m) : Prop :=
  ∀ o (ho : o≤m) (j : Fin m) i (hi : i≤(prepare m k).K) (l : Fin (prepare m k).K),
    GeneralPaperSourceMatrixStorage.window model W (GeneralPaperScoreScaleParameters.prepare m k).depth (prepare m k).S columns values o ho j i hi l≤limit

def DPBound {T m : ℕ} (model : RationalCostModel) (W k limit : ℕ)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T (prepare m k).K))
    (values : GeneralPaperRetainedFieldValues.Values m) : Prop :=
  let inputs := GeneralPaperSourceScoreStorage.matrixFields model W (GeneralPaperScoreScaleParameters.prepare m k).depth (prepare m k).S columns values
  ∀ (field : GeneralPaperExactScoreDP.Field (prepare m k).K) rest,(field::rest).Sublist inputs →
    ∀ count (hc : count≤(prepare m k).S+1) (s : Fin ((prepare m k).S+1)) xs,xs.length≤(prepare m k).K →
      GeneralPaperScoreLifetimeStorage.callerFrames model W (prepare m k).S inputs+
        GeneralPaperScoreConstructionStorage.stepWindow model W field rest count hc s xs≤limit

theorem matrix_bound_mono {T m : ℕ} (model : RationalCostModel) (W k B C : ℕ)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T (prepare m k).K))
    (values : GeneralPaperRetainedFieldValues.Values m) (hBC : B≤C) (h : MatrixBound model W k B columns values) :
    MatrixBound model W k C columns values := fun o ho j i hi l => (h o ho j i hi l).trans hBC

theorem dp_bound_mono {T m : ℕ} (model : RationalCostModel) (W k B C : ℕ)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T (prepare m k).K))
    (values : GeneralPaperRetainedFieldValues.Values m) (hBC : B≤C) (h : DPBound model W k B columns values) :
    DPBound model W k C columns values := fun field rest hSub count hc s xs hXs => (h field rest hSub count hc s xs hXs).trans hBC

def AtBound {T m : ℕ} (model : RationalCostModel) (W k limit : ℕ) (b : ℝ) (reciprocal : Bool)
    (prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K)
    (state : State (m*((prepare m k).K-1)) (m*((prepare m k).K-1))) (resident parent : ℕ)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T (prepare m k).K))
    (values : GeneralPaperRetainedFieldValues.Values m) : Prop :=
  ∃ D P M C,GeneralPaperSourceEnclosingOwners.AtBound model W k D b reciprocal prep inputs state resident ∧ parent≤P ∧
    MatrixBound model W k M columns values ∧ DPBound model W k C columns values ∧ D+P+M+C≤limit

theorem bound_mono {T m : ℕ} (model : RationalCostModel) (W k : ℕ) (b : ℝ) (reciprocal : Bool)
    (prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K)
    (state : State (m*((prepare m k).K-1)) (m*((prepare m k).K-1))) (resident parent : ℕ)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T (prepare m k).K))
    (values : GeneralPaperRetainedFieldValues.Values m) (B C : ℕ) (hBC : B≤C)
    (h : AtBound model W k B b reciprocal prep inputs state resident parent columns values) :
    AtBound model W k C b reciprocal prep inputs state resident parent columns values := by
  obtain ⟨D,P,M,F,hOld,hParent,hMatrix,hDP,hSum⟩ := h
  exact ⟨D,P,M,F,hOld,hParent,hMatrix,hDP,hSum.trans hBC⟩

theorem retained_phases {T m : ℕ} (model : RationalCostModel) (W k limit : ℕ) (b : ℝ) (reciprocal : Bool)
    (prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K)
    (state : State (m*((prepare m k).K-1)) (m*((prepare m k).K-1))) (resident parent : ℕ)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T (prepare m k).K))
    (values : GeneralPaperRetainedFieldValues.Values m)
    (h : AtBound model W k limit b reciprocal prep inputs state resident parent columns values) :
    ∀ o (ho : o≤m) (j : Fin m) i (hi : i≤(prepare m k).K) (l : Fin (prepare m k).K),
      let fields := GeneralPaperSourceScoreStorage.matrixFields model W (GeneralPaperScoreScaleParameters.prepare m k).depth (prepare m k).S columns values
      ∀ (field : GeneralPaperExactScoreDP.Field (prepare m k).K) rest,(field::rest).Sublist fields →
        ∀ count (hc : count≤(prepare m k).S+1) (s : Fin ((prepare m k).S+1)) xs,xs.length≤(prepare m k).K →
          resident+parent+GeneralPaperSourceMatrixStorage.window model W (GeneralPaperScoreScaleParameters.prepare m k).depth (prepare m k).S columns values o ho j i hi l+
            (GeneralPaperScoreLifetimeStorage.callerFrames model W (prepare m k).S fields+
              GeneralPaperScoreConstructionStorage.stepWindow model W field rest count hc s xs)≤limit := by
  obtain ⟨D,P,M,C,⟨D0,F0,_,hResident,hOldSum⟩,hParent,hMatrix,hDP,hSum⟩ := h
  intro o ho j i hi l
  dsimp only
  intro field rest hSub count hc s xs hXs
  have hm := hMatrix o ho j i hi l
  have hd := hDP field rest hSub count hc s xs hXs
  omega

theorem source_parent {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv)
    (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool)
    (hW : 1≤W) (hK : binaryWordWidth ((prepare m k).K+1)≤W) (hM : binaryWordWidth (m+1)≤W)
    (hIndex : binaryWordWidth ((prepare m k).S+2)≤W) :
    parentWindow model W k Qv hQv weights hp hs b reciprocal≤GeneralPaperSourceStrictConstructorStorageRates.parentProfile model W m k Qv := by
  let columns := GeneralPaperSourceEnclosingOwners.columns model W k Qv weights b reciprocal
  let values := (GeneralPaperRetainedFieldValues.run true model W Qv hQv weights hp hs).1
  let own := GeneralPaperInitializerPreparedPoint.ownBudget m k b reciprocal
  let opposing := GeneralPaperInitializerPreparedPoint.opposingBudget m k b reciprocal
  have hc := GeneralPaperSourceEnclosingOwners.column_data model W k Qv weights b reciprocal
  have hv := GeneralPaperRetainedFieldValues.selector_data true model W Qv hQv weights hp hs
  have hWork := GeneralPaperSourceStrictPreparationBits.actual_work model W k Qv hQv weights hp hs b hb reciprocal columns values hc hv hW hK hM hIndex
  have ho := rationalWordWidth_of_height (GeneralPaperSourceScoreHeights.own_height m k b hb reciprocal)
  have hp' := rationalWordWidth_of_height (GeneralPaperSourceStrictPreparationBits.opposing_height m k b hb reciprocal)
  have hb' := rationalWordWidth_of_height (GeneralPaperSourceScoreResidents.budget_height m k b hb reciprocal)
  change rationalWordWidth own≤_ at ho
  change rationalWordWidth opposing≤_ at hp'
  change rationalWordWidth (opposing/own)≤_ at hb'
  apply GeneralPaperRetainedStrictParentStorage.bounded model W (GeneralPaperScoreScaleParameters.prepare m k).depth (prepare m k).S
    (GeneralPaperSourceStrictConstructorStorageRates.operandWidth m k) _ (GeneralPaperScoreScaleParameters.labels_positive m k) columns values own opposing
  · unfold GeneralPaperSourceStrictConstructorStorageRates.operandWidth; omega
  · unfold GeneralPaperSourceStrictConstructorStorageRates.operandWidth; omega
  · unfold GeneralPaperSourceStrictConstructorStorageRates.operandWidth; omega
  · exact hWork

theorem source_components {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv)
    (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool)
    (hW : 1≤W) (hK : binaryWordWidth ((prepare m k).K+1)≤W) (hM : binaryWordWidth (m+1)≤W)
    (hIndex : binaryWordWidth ((prepare m k).S+2)≤W) :
    let columns := GeneralPaperSourceEnclosingOwners.columns model W k Qv weights b reciprocal
    let values := (GeneralPaperRetainedFieldValues.run true model W Qv hQv weights hp hs).1
    parentWindow model W k Qv hQv weights hp hs b reciprocal≤GeneralPaperSourceStrictConstructorStorageRates.parentProfile model W m k Qv ∧
      MatrixBound model W k (GeneralPaperSourceMatrixStorage.sourceProfile model W m k Qv) columns values ∧
      DPBound model W k (GeneralPaperSourceScoreStorage.profile model W m k) columns values := by
  have hc := GeneralPaperSourceEnclosingOwners.column_data model W k Qv weights b reciprocal
  have hv := GeneralPaperRetainedFieldValues.selector_data true model W Qv hQv weights hp hs
  refine ⟨source_parent model W k Qv hQv weights hp hs b hb reciprocal hW hK hM hIndex,?_,?_⟩
  · intro o ho j i hi l
    exact GeneralPaperSourceMatrixStorage.actual model W k Qv hQv weights hp hs b hb reciprocal _ _ hc hv hW hK hM o ho j i hi l
  · intro field rest hSub count hc' s xs hXs
    exact GeneralPaperSourceScoreStorage.actual_layer model W k Qv hQv weights hp hs b hb reciprocal _ _ hc hW hIndex field rest hSub count hc' s xs hXs

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
      parentWindow model W k Qv hQv weights hp hs b reciprocal+
      GeneralPaperSourceMatrixStorage.sourceProfile model W m k Qv+GeneralPaperSourceScoreStorage.profile model W m k≤
        GeneralPaperSourceStrictConstructorStorageRates.reservation model W m k Qv := by
  have hOld := GeneralPaperSourceEnclosingOwners.source_guard model W k Qv _hm hQv weights hp hs b hb reciprocal hModify hGuard
  have hParent := source_parent model W k Qv hQv weights hp hs b hb reciprocal hW hK hM hIndex
  unfold GeneralPaperSourceStrictConstructorStorageRates.reservation GeneralPaperSourceStrictConstructorStorageRates.sourceProfile
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
      AtBound model W k (GeneralPaperSourceStrictConstructorStorageRates.reservation model W m k Qv) b reciprocal prep inputs state
        (GeneralPaperSourceEnclosingOwners.window model W k Qv hQv weights hp hs b reciprocal)
        (parentWindow model W k Qv hQv weights hp hs b reciprocal)
        (GeneralPaperSourceEnclosingOwners.columns model W k Qv weights b reciprocal)
        (GeneralPaperRetainedFieldValues.run true model W Qv hQv weights hp hs).1 := by
  dsimp only
  intro state inv
  have hOld := GeneralPaperSourceEnclosingOwners.source_stage model W k Qv hm hQv weights hp hs b hb reciprocal hModify hGuard
    hW hK hM hIndex hDim hBatch hFinalIndex state inv
  have hC := source_components model W k Qv hQv weights hp hs b hb reciprocal hW hK hM hIndex
  refine ⟨GeneralPaperSourceEnclosingOwnerRates.reservation model W m k,
    GeneralPaperSourceStrictConstructorStorageRates.parentProfile model W m k Qv,
    GeneralPaperSourceMatrixStorage.sourceProfile model W m k Qv,GeneralPaperSourceScoreStorage.profile model W m k,
    hOld,hC.1,hC.2.1,hC.2.2,?_⟩
  unfold GeneralPaperSourceStrictConstructorStorageRates.reservation GeneralPaperSourceStrictConstructorStorageRates.sourceProfile
  omega

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
      AtBound model W k (GeneralPaperSourceStrictConstructorStorageRates.reservation model W m k Qv) b reciprocal prep inputs state
        (GeneralPaperSourceEnclosingOwners.window model W k Qv hQv weights hp hs b reciprocal)
        (parentWindow model W k Qv hQv weights hp hs b reciprocal)
        (GeneralPaperSourceEnclosingOwners.columns model W k Qv weights b reciprocal)
        (GeneralPaperRetainedFieldValues.run true model W Qv hQv weights hp hs).1 := by
  let prep := GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b reciprocal
  let v := GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs
  let f := (GeneralPaperProxyClassifier.classify m k b).choice.proxy
  let inputs := GeneralPaperSharedBasisInputs.prepare k prep v f.num f.den reciprocal
  have hStart := GeneralPaperSourceBasisInputValidity.actual_start k Qv hm hQv weights hp hs b hb reciprocal
  have hN : 0 < inputs.controls.N := (GeneralPaperInitializerSelectedControls.positive m k hm b hb reciprocal).1
  obtain ⟨state,hr,inv⟩ := GeneralPaperBasisControllerSound.stages_valid (GeneralPaperScoreScaleParameters.prepare m k).depth
    prep.dictionary v (GeneralPaperScoreScaleParameters.labels_positive m k) (prepare m k).S prep.threshold inputs.controls.N hN
    (GeneralPaperScoreScaleParameters.score_cap m k) inputs.betaN inputs.initialGrid (hStart) (m*((prepare m k).K-1)) le_rfl
  have hReturn : GeneralPaperBasisController.stages prep.dictionary.label inputs.matrix (prepare m k).S prep.threshold
      inputs.controls.N inputs.betaN inputs.initialGrid (m*((prepare m k).K-1)) le_rfl=some state := by
    rw [GeneralPaperSharedBasisInputs.matrix_eq]; exact hr
  refine ⟨state,?_,source_stage model W k Qv hm hQv weights hp hs b hb reciprocal hModify hGuard hW hK hM hIndex hDim hBatch hFinalIndex state inv⟩
  exact (GeneralPaperBasisControllerBits.stages_data model W _ _ _ _ _ _ _ _ _).trans hReturn

end Blotto.GeneralPaperSourceStrictConstructorStorage
