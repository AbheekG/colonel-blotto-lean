import Blotto.GeneralPaperSourceEndpointFractionConstructionStorageRates

/-! Full actual endpoint-fraction constructor and all native paths.
Source cell/root/classifier facts supply every raw-word and record bound.
Its window explicitly coexists with the complete previous outer endpoint
and every earlier phase reserve. No constructor reruns classification. -/
namespace Blotto.GeneralPaperSourceEndpointFractionConstructionStorage
open RationalOrderCell GeneralPaperProxyParameters GeneralPaperBasisStoredProducts
open GeneralPaperBasisState GeneralPaperBasisInvariant GeneralPaperEncodedScalarStorage
open GeneralPaperEncodedBasisStorage (integerBits arrayFootprint arrayProfile)
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 18000000
set_option maxRecDepth 16384

noncomputable def window (model : RationalCostModel) (W m k : ℕ) (b : ℝ) : ℕ :=
  GeneralPaperEndpointFractionConstructionStorage.window model W (prepare m k).Qg (grid_positive m k)
    (GeneralPaperProxyClassifier.classify m k b)

def AtBound {T m : ℕ} (model : RationalCostModel) (W k limit : ℕ) (b : ℝ) (reciprocal : Bool)
    (prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K)
    (state : State (m*((prepare m k).K-1)) (m*((prepare m k).K-1))) : Prop :=
  ∃ previousReserve returnReserve,GeneralPaperSourceOuterEndpointStorage.AtBound model W k previousReserve b reciprocal prep inputs state ∧
    window model W m k b≤returnReserve ∧ previousReserve+returnReserve≤limit

theorem bound_mono {T m : ℕ} (model : RationalCostModel) (W k : ℕ) (b : ℝ) (reciprocal : Bool)
    (prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K)
    (state : State (m*((prepare m k).K-1)) (m*((prepare m k).K-1))) (B C : ℕ) (hBC : B≤C)
    (h : AtBound model W k B b reciprocal prep inputs state) : AtBound model W k C b reciprocal prep inputs state := by
  obtain ⟨D,F,hPrevious,hReturns,hSum⟩ := h
  exact ⟨D,F,hPrevious,hReturns,hSum.trans hBC⟩

theorem retained_outer {T m : ℕ} (model : RationalCostModel) (W k limit : ℕ) (b : ℝ) (reciprocal : Bool)
    (prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K)
    (state : State (m*((prepare m k).K-1)) (m*((prepare m k).K-1)))
    (h : AtBound model W k limit b reciprocal prep inputs state) :
    GeneralPaperSourceOuterEndpointStorage.window model W k b reciprocal prep inputs+
      window model W m k b≤limit := by
  obtain ⟨D,F,⟨D0,F0,_,hPacking,hOldSum⟩,hReturns,hSum⟩ := h
  exact (Nat.add_le_add (hPacking.trans (show F0≤D by omega)) hReturns).trans hSum

theorem source_constructor (model : RationalCostModel) (W m k : ℕ) (b : ℝ) (hb : 0<b ∧ b<1) :
    window model W m k b≤GeneralPaperSourceEndpointFractionConstructionStorageRates.sourceProfile model W m k ∧
      (GeneralPaperRetainedEndpointFraction.run model.rat W (prepare m k).Qg (grid_positive m k)
        (GeneralPaperProxyClassifier.classify m k b)).2≤64*W+2*model.rat (GeneralPaperSourceEndpointFractionConstructionStorageRates.operandWidth m k) := by
  let c := GeneralPaperProxyClassifier.classify m k b
  let B := (prepare m k).qbar
  let R := GeneralPaperSourceEndpointFractionConstructionStorageRates.operandWidth m k
  have hGrid : (prepare m k).Qg≤B := by
    dsimp only [B]
    rw [(GeneralPaperProxyParameters.data m k).2.2.2.2.2.2]
    omega
  have hCell : c.cell+1≤B := by
    have h := (GeneralPaperProxyQuotient.locate_spec m k b hb).1
    change c.cell<(prepare m k).Qg at h
    omega
  have hRoot : ∀ f,c.root=some f → f.num≤B ∧ f.den≤B := by
    intro f hf
    have h := GeneralPaperClassifierResultStorage.root_caps m k b hb f hf
    dsimp only [B]
    simpa only [(GeneralPaperProxyParameters.data m k).2.2.2.2.2.2] using h
  have hR : natBits B≤R := by
    unfold natBits R GeneralPaperSourceEndpointFractionConstructionStorageRates.operandWidth GeneralPaperRetainedEndpointBitBounds.priceWidth
    dsimp only [B]
    omega
  refine ⟨GeneralPaperEndpointFractionConstructionStorage.bounded model W (prepare m k).Qg B R _ (grid_positive m k) c
    (GeneralPaperClassifierResultStorage.native W m k b hb) hCell hGrid hRoot hR,?_⟩
  rw [GeneralPaperEndpointFractionConstructionStorage.run_work]
  exact Nat.add_le_add_left (GeneralPaperEndpointFractionConstructionStorage.addition_bound model B R c hCell hR) _

theorem source_guard {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (_hm : 0<m) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv)
    (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool)
    (hModify : (GeneralPaperProxyClassifier.classify m k b).choice.modify≠none)
    (hGuard : reciprocal=true ∧ (GeneralPaperProxyClassifier.classify m k b).choice.endpoint=0) :
    let prep := GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b reciprocal
    let v := GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs
    let f := (GeneralPaperProxyClassifier.classify m k b).choice.proxy
    let inputs := GeneralPaperSharedBasisInputs.prepare k prep v f.num f.den reciprocal
    GeneralPaperSourceOuterEndpointStorage.window model W k b reciprocal prep inputs+window model W m k b≤
      GeneralPaperSourceEndpointFractionConstructionStorageRates.reservation model W m k := by
  have hOld := (GeneralPaperSourceOuterEndpointStorage.source_guard model W k Qv _hm hQv weights hp hs b hb reciprocal hModify hGuard).1
  have hNew := (source_constructor model W m k b hb).1
  have hp : GeneralPaperSourceOuterEndpointStorageRates.sourceProfile model W m k≤GeneralPaperSourceOuterEndpointStorageRates.reservation model W m k :=
    Nat.le_add_left _ _
  exact Nat.add_le_add (hOld.trans hp) hNew

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
      AtBound model W k (GeneralPaperSourceEndpointFractionConstructionStorageRates.reservation model W m k) b reciprocal prep inputs state := by
  dsimp only
  intro state inv
  have hOld := GeneralPaperSourceOuterEndpointStorage.source_stage model W k Qv hm hQv weights hp hs b hb reciprocal hModify hGuard
    hW hK hM hIndex hDim hBatch hFinalIndex state inv
  exact ⟨GeneralPaperSourceOuterEndpointStorageRates.reservation model W m k,
    GeneralPaperSourceEndpointFractionConstructionStorageRates.sourceProfile model W m k,hOld,
    (source_constructor model W m k b hb).1,le_rfl⟩

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
      AtBound model W k (GeneralPaperSourceEndpointFractionConstructionStorageRates.reservation model W m k) b reciprocal prep inputs state := by
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

end Blotto.GeneralPaperSourceEndpointFractionConstructionStorage
