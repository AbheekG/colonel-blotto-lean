import Blotto.GeneralPaperSourceOuterEndpointStorageRates

/-! Actual outer source endpoint ownership, full returned input/basis
and optional point, native branch fields and uniform work. The selected
source final invariant supplies every child bound. Early guard rejection
has no child-state premises. All preceding reserves remain explicitly joined. -/
namespace Blotto.GeneralPaperSourceOuterEndpointStorage
open RationalOrderCell GeneralPaperProxyParameters GeneralPaperBasisStoredProducts
open GeneralPaperBasisState GeneralPaperBasisInvariant GeneralPaperEncodedScalarStorage
open GeneralPaperEncodedBasisStorage (integerBits arrayFootprint arrayProfile)
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 18000000
set_option maxRecDepth 8192

noncomputable def window {T m : ℕ} (model : RationalCostModel) (W k : ℕ) (b : ℝ) (reciprocal : Bool)
    (prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K) : ℕ :=
  let f := (GeneralPaperProxyClassifier.classify m k b).choice.proxy
  GeneralPaperOuterEndpointFrameStorage.window model W (prepare m k).H f.num f.den reciprocal prep inputs.matrix
    (GeneralPaperSourceFinalCheckStorage.endpointFraction model W m k b) (GeneralPaperProxyClassifier.classify m k b).choice.endpoint

def AtBound {T m : ℕ} (model : RationalCostModel) (W k limit : ℕ) (b : ℝ) (reciprocal : Bool)
    (prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K)
    (state : State (m*((prepare m k).K-1)) (m*((prepare m k).K-1))) : Prop :=
  ∃ previousReserve returnReserve,GeneralPaperSourceInitializerReturnStorage.AtBound model W k previousReserve b reciprocal prep inputs state ∧
    window model W k b reciprocal prep inputs≤returnReserve ∧ previousReserve+returnReserve≤limit

theorem bound_mono {T m : ℕ} (model : RationalCostModel) (W k : ℕ) (b : ℝ) (reciprocal : Bool)
    (prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K)
    (state : State (m*((prepare m k).K-1)) (m*((prepare m k).K-1))) (B C : ℕ) (hBC : B≤C)
    (h : AtBound model W k B b reciprocal prep inputs state) : AtBound model W k C b reciprocal prep inputs state := by
  obtain ⟨D,F,hPrevious,hReturns,hSum⟩ := h
  exact ⟨D,F,hPrevious,hReturns,hSum.trans hBC⟩

theorem retained_initializer {T m : ℕ} (model : RationalCostModel) (W k limit : ℕ) (b : ℝ) (reciprocal : Bool)
    (prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K)
    (state : State (m*((prepare m k).K-1)) (m*((prepare m k).K-1)))
    (h : AtBound model W k limit b reciprocal prep inputs state) :
    GeneralPaperSourceInitializerReturnStorage.window model W k b reciprocal prep inputs+
      window model W k b reciprocal prep inputs≤limit := by
  obtain ⟨D,F,⟨D0,F0,_,hPacking,hOldSum⟩,hReturns,hSum⟩ := h
  exact (Nat.add_le_add (hPacking.trans (show F0≤D by omega)) hReturns).trans hSum

theorem source_outer {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv)
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
    window model W k b reciprocal prep inputs≤GeneralPaperSourceOuterEndpointStorageRates.sourceProfile model W m k ∧
      (GeneralPaperRetainedBasisEndpointBits.run model W (prepare m k).H f.num f.den reciprocal prep inputs.matrix
        (GeneralPaperSourceFinalCheckStorage.endpointFraction model W m k b) (GeneralPaperProxyClassifier.classify m k b).choice.endpoint).2≤
        GeneralPaperSourceOuterEndpointStorageRates.price model W m k := by
  dsimp only
  let prep := GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b reciprocal
  let v := GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs
  let f := (GeneralPaperProxyClassifier.classify m k b).choice.proxy
  let inputs := GeneralPaperSharedBasisInputs.prepare k prep v f.num f.den reciprocal
  let endpoint := GeneralPaperSourceFinalCheckStorage.endpointFraction model W m k b
  let value := (GeneralPaperProxyClassifier.classify m k b).choice.endpoint
  have hDim1 := (binaryWordWidth_mono (show m*((prepare m k).K-1)+1≤m*((prepare m k).K-1)+3 by omega)).trans hDim
  have hf := GeneralPaperProxyClassifier.proxy_integer_representation m k b hb
  have hInputData := GeneralPaperRetainedBasisInputs.actual_data true model W k f.num f.den reciprocal prep v inputs.matrix
    (GeneralPaperSharedBasisInputs.matrix_eq k prep v f.num f.den reciprocal) hm hf.1 f.den_pos
  obtain ⟨state,hReturn,inv,_⟩ := GeneralPaperSharedBasisBits.actual_return model W k Qv hm hQv weights hp hs b hb reciprocal
    hW hDim hIndex hBatch hFinalIndex
  have hInputs := GeneralPaperSourceInitializerReturnStorage.source_returns model W k Qv hm hQv weights hp hs b hb reciprocal hW hK hM hDim1
  have hInputOwner : GeneralPaperRetainedInputsReturnStorage.window model W (prepare m k).H f.num f.den reciprocal prep inputs.matrix≤
      GeneralPaperSourceInitializerReturnStorageRates.sourceProfile model W m k := by
    have h := hInputs.1
    change GeneralPaperInitializerGridReturnStorage.window model W inputs.controls.N inputs.controls.depth prep.dictionary+
      GeneralPaperRetainedInputsReturnStorage.window model W (prepare m k).H f.num f.den reciprocal prep inputs.matrix≤_ at h
    omega
  have hBasisWork := GeneralPaperSourceBasisControllerStorage.prefix_work model W k Qv hm hQv weights hp hs b hb reciprocal
    hW hDim hIndex hBatch hFinalIndex (m*((prepare m k).K-1)) le_rfl
  have hContinue := GeneralPaperSourceEndpointContinuationReturnBounds.source_bounds model W k Qv hm hQv weights hp hs b hb reciprocal
    hModify hGuard hW hK hM hIndex hDim1 state inv
  have hScalar := GeneralPaperSourceEndpointScalarStorage.source_scalars model W m k b hb hModify reciprocal
  have hValue := GeneralPaperEndpointRatioSize.height m k b hb hModify
  have hGuardPrice := GeneralPaperRetainedEndpointBitBounds.guard_price model W (prepare m k).qbar value hValue
  have hFraction := GeneralPaperRetainedEndpointBitBounds.fraction_bounds model.rat W m k b hb hModify
  have hEndpointPrice := GeneralPaperRetainedEndpointBitBounds.endpoint_price model W (prepare m k).qbar endpoint value
    hFraction.1 hFraction.2 hValue reciprocal
  have hTotal := GeneralPaperSourceEndpointBitPrice.work_of_return model W (prepare m k).H f.num f.den _ _ _ reciprocal prep inputs.matrix
    endpoint value hGuard inputs hInputData state hReturn hInputs.2.1 hBasisWork hContinue.1
  have hWork : (GeneralPaperRetainedBasisEndpointBits.run model W (prepare m k).H f.num f.den reciprocal prep inputs.matrix endpoint value).2≤
      GeneralPaperSourceOuterEndpointStorageRates.price model W m k :=
    hTotal.trans (GeneralPaperSourceEndpointBitPrice.sum_bound _ _ _ _ _ _ _ hGuardPrice hEndpointPrice)
  have hPoint : GeneralPaperRawEndpointReturnStorage.optionFoot W
      (GeneralPaperRetainedBasisEndpointBits.run model W (prepare m k).H f.num f.den reciprocal prep inputs.matrix endpoint value).1≤
      GeneralPaperSourceEndpointContinuationReturnBounds.pointProfile W m k := by
    rw [GeneralPaperRetainedBasisEndpointBits.run,ite_eq_right hGuard]
    dsimp only
    rw [hInputData,hReturn]
    exact hContinue.2.1
  have hBasis : ∀ s,(GeneralPaperSharedBasisBits.run model W prep
      (GeneralPaperRetainedBasisInputs.run true model W (prepare m k).H f.num f.den reciprocal prep inputs.matrix).1).1=some s →
        GeneralPaperEncodedBasisStorage.footprint W s≤GeneralPaperEncodedBasisStorage.paperProfile W m k := by
    intro s hr
    rw [hInputData,hReturn] at hr
    have he : state=s := Option.some.inj hr
    subst s
    exact hContinue.2.2
  refine ⟨?_,hWork⟩
  exact GeneralPaperOuterEndpointFrameStorage.bounded model W (prepare m k).H f.num f.den _ _ _ _ _ reciprocal prep inputs.matrix
    endpoint value hScalar (fun _ => hInputOwner) (fun _ => hBasis) hPoint hWork

theorem source_guard {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (_hm : 0<m) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv)
    (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool)
    (hModify : (GeneralPaperProxyClassifier.classify m k b).choice.modify≠none)
    (hGuard : reciprocal=true ∧ (GeneralPaperProxyClassifier.classify m k b).choice.endpoint=0) :
    let prep := GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b reciprocal
    let v := GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs
    let f := (GeneralPaperProxyClassifier.classify m k b).choice.proxy
    let inputs := GeneralPaperSharedBasisInputs.prepare k prep v f.num f.den reciprocal
    window model W k b reciprocal prep inputs≤GeneralPaperSourceOuterEndpointStorageRates.sourceProfile model W m k ∧
      GeneralPaperRetainedBasisEndpointBits.run model W (prepare m k).H f.num f.den reciprocal prep inputs.matrix
        (GeneralPaperSourceFinalCheckStorage.endpointFraction model W m k b) (GeneralPaperProxyClassifier.classify m k b).choice.endpoint=
          (none,GeneralPaperRetainedBasisEndpointBits.guardPrice model W (GeneralPaperProxyClassifier.classify m k b).choice.endpoint) := by
  dsimp only
  let prep := GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b reciprocal
  let v := GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs
  let f := (GeneralPaperProxyClassifier.classify m k b).choice.proxy
  let inputs := GeneralPaperSharedBasisInputs.prepare k prep v f.num f.den reciprocal
  let endpoint := GeneralPaperSourceFinalCheckStorage.endpointFraction model W m k b
  let value := (GeneralPaperProxyClassifier.classify m k b).choice.endpoint
  have hScalar := GeneralPaperSourceEndpointScalarStorage.source_scalars model W m k b hb hModify reciprocal
  have hValue := GeneralPaperEndpointRatioSize.height m k b hb hModify
  have hPrice := GeneralPaperRetainedEndpointBitBounds.guard_price model W (prepare m k).qbar value hValue
  have hPriceCap : GeneralPaperRetainedBasisEndpointBits.guardPrice model W value≤GeneralPaperSourceOuterEndpointStorageRates.price model W m k := by
    unfold GeneralPaperSourceOuterEndpointStorageRates.price
    omega
  refine ⟨?_,?_⟩
  · exact GeneralPaperOuterEndpointFrameStorage.guard_bound model W (prepare m k).H f.num f.den _ _ _ _ _ reciprocal prep inputs.matrix
      endpoint value hGuard hScalar (by unfold GeneralPaperSourceEndpointContinuationReturnBounds.pointProfile GeneralPaperRawEndpointReturnStorage.optionProfile; omega) hPriceCap
  · exact ite_eq_left hGuard

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
      AtBound model W k (GeneralPaperSourceOuterEndpointStorageRates.reservation model W m k) b reciprocal prep inputs state := by
  dsimp only
  intro state inv
  have hOld := GeneralPaperSourceInitializerReturnStorage.source_stage model W k Qv hm hQv weights hp hs b hb reciprocal hModify hGuard
    hW hK hM hIndex hDim hBatch hFinalIndex state inv
  exact ⟨GeneralPaperSourceInitializerReturnStorageRates.reservation model W m k,
    GeneralPaperSourceOuterEndpointStorageRates.sourceProfile model W m k,hOld,
    (source_outer model W k Qv hm hQv weights hp hs b hb reciprocal hModify hGuard hW hK hM hIndex hDim hBatch hFinalIndex).1,le_rfl⟩

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
      AtBound model W k (GeneralPaperSourceOuterEndpointStorageRates.reservation model W m k) b reciprocal prep inputs state := by
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

end Blotto.GeneralPaperSourceOuterEndpointStorage
