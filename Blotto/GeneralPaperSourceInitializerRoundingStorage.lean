import Blotto.GeneralPaperSourceInitializerRoundingStorageRates

/-! One active actual source anchor rounding, with full native quotient
and rounding parent storage. The source supplies original N/depth, unit
anchors and heights. All old initializer/controller/stage/endpoint/source
reserves remain; these scalar windows are not summed over all m*K entries. -/
namespace Blotto.GeneralPaperSourceInitializerRoundingStorage
open RationalOrderCell GeneralPaperProxyParameters GeneralPaperBasisStoredProducts
open GeneralPaperBasisState GeneralPaperBasisInvariant
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 8192

def window {T m : ℕ} (model : RationalCostModel) (W k : ℕ)
    (prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K) (j : Fin m) (l : Fin (prepare m k).K) : ℕ :=
  GeneralPaperInitializerRoundingStorage.window model W inputs.controls.N inputs.controls.depth (prep.dictionary.anchor j l)

def AtBound {T m : ℕ} (model : RationalCostModel) (W k limit : ℕ) (b : ℝ) (reciprocal : Bool)
    (prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K)
    (state : State (m*((prepare m k).K-1)) (m*((prepare m k).K-1))) : Prop :=
  ∃ previousReserve roundingReserve,GeneralPaperSourceInitializerControlStorage.AtBound model W k previousReserve b reciprocal prep inputs state ∧
    (∀ j l,window model W k prep inputs j l≤roundingReserve) ∧ previousReserve+roundingReserve≤limit

theorem bound_mono {T m : ℕ} (model : RationalCostModel) (W k : ℕ) (b : ℝ) (reciprocal : Bool)
    (prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K)
    (state : State (m*((prepare m k).K-1)) (m*((prepare m k).K-1))) (B C : ℕ) (hBC : B≤C)
    (h : AtBound model W k B b reciprocal prep inputs state) : AtBound model W k C b reciprocal prep inputs state := by
  obtain ⟨D,F,hPrevious,hRounding,hSum⟩ := h
  exact ⟨D,F,hPrevious,hRounding,hSum.trans hBC⟩

theorem retained_controls {T m : ℕ} (model : RationalCostModel) (W k limit : ℕ) (b : ℝ) (reciprocal : Bool)
    (prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K)
    (state : State (m*((prepare m k).K-1)) (m*((prepare m k).K-1)))
    (h : AtBound model W k limit b reciprocal prep inputs state) :
    ∀ j l,GeneralPaperSourceInitializerControlStorage.window model W m k b reciprocal+window model W k prep inputs j l≤limit := by
  obtain ⟨D,F,⟨D0,F0,_,hControls,hOldSum⟩,hRounding,hSum⟩ := h
  intro j l
  exact (Nat.add_le_add (hControls.trans (show F0≤D by omega)) (hRounding j l)).trans hSum

theorem source_rounding {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv)
    (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool) :
    let prep := GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b reciprocal
    let v := GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs
    let f := (GeneralPaperProxyClassifier.classify m k b).choice.proxy
    let inputs := GeneralPaperSharedBasisInputs.prepare k prep v f.num f.den reciprocal
    ∀ j l,window model W k prep inputs j l≤GeneralPaperSourceInitializerRoundingStorageRates.sourceProfile model W m k := by
  dsimp only
  intro j l
  let prep := GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b reciprocal
  let v := GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs
  let f := (GeneralPaperProxyClassifier.classify m k b).choice.proxy
  let inputs := GeneralPaperSharedBasisInputs.prepare k prep v f.num f.den reciprocal
  let G := GeneralPaperSourceRayStorageWidth.gridWord m k
  have hN : 0 < inputs.controls.N := (GeneralPaperInitializerSelectedControls.positive m k hm b hb reciprocal).1
  have hGrid := GeneralPaperSourceRayStorageWidth.grid_bound m k b hb reciprocal
  change binaryWordWidth inputs.controls.N≤G at hGrid
  have hDepth : inputs.controls.depth≤G+1 := by
    have h := GeneralPaperPowerCeiling.loop_depth inputs.controls.N 1 (by decide)
    change (GeneralPaperPowerCeiling.ceiling inputs.controls.N).doublings≤binaryWordWidth inputs.controls.N at h
    change (GeneralPaperPowerCeiling.ceiling inputs.controls.N).doublings+1≤G+1
    omega
  have hCap : inputs.controls.N<2^inputs.controls.depth := GeneralPaperInitializerParameters.quotient_cap m (prepare m k).H f.num f.den reciprocal
  have hUnit := GeneralPaperSourceUnchangedDictionary.unit k Qv hm hQv weights hp hs b hb reciprocal
  have hHeight := GeneralPaperSourceScoreHeights.prepared_anchors k Qv hQv weights hp hs b hb reciprocal j l
  have hWidth : GeneralPaperInitializerRoundingBits.width (GeneralPaperSourceScoreHeights.anchorHeight m k)
      inputs.controls.N inputs.controls.depth≤GeneralPaperSourceInitializerRoundingStorageRates.operandWidth m k := by
    unfold GeneralPaperInitializerRoundingBits.width GeneralPaperSourceInitializerRoundingStorageRates.operandWidth
    dsimp only [G] at hGrid hDepth
    omega
  exact GeneralPaperInitializerRoundingStorage.bounded model W inputs.controls.N inputs.controls.depth
    (GeneralPaperSourceScoreHeights.anchorHeight m k) (GeneralPaperSourceInitializerRoundingStorageRates.operandWidth m k)
    hN hCap (prep.dictionary.anchor j l) ⟨hUnit.nonnegative j l,hUnit.bounded j l⟩ hHeight hWidth

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
      AtBound model W k (GeneralPaperSourceInitializerRoundingStorageRates.reservation model W m k) b reciprocal prep inputs state := by
  dsimp only
  intro state inv
  have hOld := GeneralPaperSourceInitializerControlStorage.source_stage model W k Qv hm hQv weights hp hs b hb reciprocal hModify hGuard
    hW hK hM hIndex hDim hBatch hFinalIndex state inv
  exact ⟨GeneralPaperSourceInitializerControlStorageRates.reservation model W m k,
    GeneralPaperSourceInitializerRoundingStorageRates.sourceProfile model W m k,hOld,
    source_rounding model W k Qv hm hQv weights hp hs b hb reciprocal,le_rfl⟩

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
      AtBound model W k (GeneralPaperSourceInitializerRoundingStorageRates.reservation model W m k) b reciprocal prep inputs state := by
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

end Blotto.GeneralPaperSourceInitializerRoundingStorage
