import Blotto.GeneralPaperSourceBasisControllerStorageRates

/-! Native basis-controller initialization, pending ancestors and one
active return frame coexist with every earlier reached stage window.
The original source supplies every prefix work bound. No whole basis state
is summed over recursion depth; full active states remain in old reserves. -/
namespace Blotto.GeneralPaperSourceBasisControllerStorage
open RationalOrderCell GeneralPaperProxyParameters GeneralPaperBasisStoredProducts
open GeneralPaperBasisState GeneralPaperBasisInvariant
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 14000000
set_option maxRecDepth 8192

def window {T m : ℕ} (model : RationalCostModel) (W k : ℕ)
    (prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K) (j : ℕ) (hj : j≤m*((prepare m k).K-1)) : ℕ :=
  GeneralPaperBasisControllerFrameStorage.window model W prep.dictionary.label inputs.matrix (prepare m k).S prep.threshold
    inputs.controls.N inputs.betaN inputs.initialGrid j hj

def AtBound {T m : ℕ} (model : RationalCostModel) (W k limit : ℕ) (b : ℝ) (reciprocal : Bool)
    (prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K)
    (state : State (m*((prepare m k).K-1)) (m*((prepare m k).K-1))) : Prop :=
  ∃ previousReserve controllerReserve,GeneralPaperSourceEndpointScalarStorage.AtBound model W k previousReserve b reciprocal prep inputs state ∧
    (∀ j (hj : j≤m*((prepare m k).K-1)),window model W k prep inputs j hj≤controllerReserve) ∧ previousReserve+controllerReserve≤limit

theorem bound_mono {T m : ℕ} (model : RationalCostModel) (W k : ℕ) (b : ℝ) (reciprocal : Bool)
    (prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K)
    (state : State (m*((prepare m k).K-1)) (m*((prepare m k).K-1))) (B C : ℕ) (hBC : B≤C)
    (h : AtBound model W k B b reciprocal prep inputs state) : AtBound model W k C b reciprocal prep inputs state := by
  obtain ⟨D,F,hPrevious,hController,hSum⟩ := h
  exact ⟨D,F,hPrevious,hController,hSum.trans hBC⟩

theorem retained_scalars {T m : ℕ} (model : RationalCostModel) (W k limit : ℕ) (b : ℝ) (reciprocal : Bool)
    (prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K)
    (state : State (m*((prepare m k).K-1)) (m*((prepare m k).K-1)))
    (h : AtBound model W k limit b reciprocal prep inputs state) :
    ∀ j hj,GeneralPaperSourceEndpointScalarStorage.window model W m k b reciprocal+window model W k prep inputs j hj≤limit := by
  obtain ⟨D,F,⟨D0,F0,_,hScalars,hOldSum⟩,hController,hSum⟩ := h
  intro j hj
  exact (Nat.add_le_add (hScalars.trans (show F0≤D by omega)) (hController j hj)).trans hSum

theorem retained_advance {T m : ℕ} (model : RationalCostModel) (W k limit : ℕ) (b : ℝ) (reciprocal : Bool)
    (prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K)
    (finalState : State (m*((prepare m k).K-1)) (m*((prepare m k).K-1)))
    (h : AtBound model W k limit b reciprocal prep inputs finalState) (j : ℕ) (hj : j<m*((prepare m k).K-1)) :
    ∃ state,(GeneralPaperBasisControllerBits.stages model W prep.dictionary.label inputs.matrix (prepare m k).S prep.threshold
      inputs.controls.N inputs.betaN inputs.initialGrid j (Nat.le_of_lt hj)).1=some state ∧
      ∃ answer,(GeneralPaperSourceBasisAdvanceStorage.endpoint model W k prep inputs state hj).1=some answer ∧
        ∀ p a current (hc : current≤m*((prepare m k).K-1)),
          GeneralPaperSourceBasisAdvanceStorage.window model W k p a prep inputs state hj answer+
            window model W k prep inputs current hc≤limit := by
  obtain ⟨D,F,hScalars,hController,hSum⟩ := h
  obtain ⟨D0,F0,hFinal,_,hSum0⟩ := hScalars
  obtain ⟨D1,F1,hChecks,_,hSum1⟩ := hFinal
  obtain ⟨D2,F2,hRaw,_,hSum2⟩ := hChecks
  obtain ⟨D3,F3,hAffine,_,hSum3⟩ := hRaw
  obtain ⟨D4,F4,hEarlier,_,hSum4⟩ := hAffine
  obtain ⟨state,hr,⟨D5,F5,_,⟨answer,ha,hAdvance⟩,hSum5⟩⟩ := hEarlier j hj
  refine ⟨state,hr,answer,ha,?_⟩
  intro p a current hc
  exact (Nat.add_le_add ((hAdvance p a).trans (show F5≤D by omega)) (hController current hc)).trans hSum

theorem prefix_work {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv)
    (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool)
    (hW : 1≤W) (hDim : binaryWordWidth (m*((prepare m k).K-1)+3)≤W)
    (hIndex : binaryWordWidth ((prepare m k).S+2)≤W)
    (hBatch : binaryWordWidth (((prepare m k).S+1)*((prepare m k).K*(prepare m k).K)+3)≤W)
    (hFinalIndex : binaryWordWidth ((prepare m k).S+4)≤W) :
    let prep := GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b reciprocal
    let v := GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs
    let f := (GeneralPaperProxyClassifier.classify m k b).choice.proxy
    let inputs := GeneralPaperSharedBasisInputs.prepare k prep v f.num f.den reciprocal
    ∀ j (hj : j≤m*((prepare m k).K-1)),
      (GeneralPaperBasisControllerBits.stages model W prep.dictionary.label inputs.matrix (prepare m k).S prep.threshold
        inputs.controls.N inputs.betaN inputs.initialGrid j hj).2≤GeneralPaperSourceBasisControllerStorageRates.workPrice model W m k := by
  dsimp only
  intro j hj
  let prep := GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b reciprocal
  let v := GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs
  let f := (GeneralPaperProxyClassifier.classify m k b).choice.proxy
  let inputs := GeneralPaperSharedBasisInputs.prepare k prep v f.num f.den reciprocal
  let T := (GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows
  let R := GeneralPaperSourceBasisControllerStorageRates.operandWidth m k
  have hGridWord := GeneralPaperSourceRayStorageWidth.grid_bound m k b hb reciprocal
  change binaryWordWidth inputs.controls.N≤GeneralPaperSourceRayStorageWidth.gridWord m k at hGridWord
  have hWidth : GeneralPaperBasisBitEnvelope.width m k inputs.controls.N (prepare m k).S T≤R := by
    unfold GeneralPaperBasisBitEnvelope.width R GeneralPaperSourceBasisControllerStorageRates.operandWidth
      GeneralPaperSourceFinalEndpointReturnRates.operandWidth GeneralPaperSourceFinalCheckStorageRates.operandWidth
      GeneralPaperSourceRawAffineStorageRates.operandWidth GeneralPaperSourceRayStorageWidth.width GeneralPaperSourceRayStorageWidth.rootWidth
    dsimp only [T]
    ring_nf
    omega
  have hPrice := model.monotone hWidth
  have hStep : GeneralPaperBasisStepBits.profile T m (prepare m k).K (prepare m k).S W
      (model.rat (GeneralPaperBasisBitEnvelope.width m k inputs.controls.N (prepare m k).S T))≤
      GeneralPaperBasisStepBits.profile T m (prepare m k).K (prepare m k).S W (model.rat R) := by
    unfold GeneralPaperBasisStepBits.profile
    exact Nat.add_le_add (Nat.mul_le_mul_left _ (Nat.add_le_add_left hPrice W))
      (GeneralPaperBasisBitEnvelope.endpoint_profile_mono _ _ _ _ _ _ _ hPrice)
  have hN : 0 < inputs.controls.N := (GeneralPaperInitializerSelectedControls.positive m k hm b hb reciprocal).1
  have hNative := GeneralPaperBasisControllerBits.stages_work model W k hm (GeneralPaperScoreScaleParameters.prepare m k).depth
    prep.dictionary v (prepare m k).S prep.threshold inputs.controls.N hN (GeneralPaperScoreScaleParameters.score_cap m k)
    inputs.betaN inputs.initialGrid (GeneralPaperSourceBasisGridSize.auxiliary (m:=m) k b hb reciprocal)
    (GeneralPaperSourceBasisGridSize.grid k Qv hm hQv weights hp hs b hb reciprocal)
    (GeneralPaperSourceBasisInputValidity.actual_start k Qv hm hQv weights hp hs b hb reciprocal)
    hW hDim hIndex hBatch hFinalIndex j hj
  rw [GeneralPaperSharedBasisInputs.matrix_eq]
  apply hNative.trans
  exact Nat.add_le_add_left (Nat.mul_le_mul hj (Nat.add_le_add_right hStep (24*W))) (72*W)

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
      AtBound model W k (GeneralPaperSourceBasisControllerStorageRates.reservation model W m k) b reciprocal prep inputs state := by
  dsimp only
  intro state inv
  let prep := GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b reciprocal
  let v := GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs
  let f := (GeneralPaperProxyClassifier.classify m k b).choice.proxy
  let inputs := GeneralPaperSharedBasisInputs.prepare k prep v f.num f.den reciprocal
  have hDim1 := (binaryWordWidth_mono (show m*((prepare m k).K-1)+1≤m*((prepare m k).K-1)+3 by omega)).trans hDim
  have hOld := GeneralPaperSourceEndpointScalarStorage.source_stage model W k Qv hm hQv weights hp hs b hb reciprocal hModify hGuard
    hW hK hM hIndex hDim1 hBatch hFinalIndex state inv
  have hWork := prefix_work model W k Qv hm hQv weights hp hs b hb reciprocal hW hDim hIndex hBatch hFinalIndex
  refine ⟨GeneralPaperSourceEndpointScalarStorageRates.reservation model W m k,
    GeneralPaperSourceBasisControllerStorageRates.sourceProfile model W m k,hOld,?_,le_rfl⟩
  intro j hj
  exact GeneralPaperBasisControllerFrameStorage.bounded model W (GeneralPaperSourceBasisControllerStorageRates.workPrice model W m k)
    prep.dictionary.label inputs.matrix (prepare m k).S prep.threshold inputs.controls.N inputs.betaN inputs.initialGrid hW hWork j hj

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
      AtBound model W k (GeneralPaperSourceBasisControllerStorageRates.reservation model W m k) b reciprocal prep inputs state := by
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

end Blotto.GeneralPaperSourceBasisControllerStorage
