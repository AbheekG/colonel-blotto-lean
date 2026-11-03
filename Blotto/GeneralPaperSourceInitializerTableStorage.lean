import Blotto.GeneralPaperSourceInitializerTableStorageRates

/-! Complete actual source stored-anchor constructors. Full native
outer/inner buffers retain original quotient/rational pairs and one active
inner fill. Prior active rounding scratch coexists explicitly, independently
of both constructor cursors, without summing scalar scratch over m*K. -/
namespace Blotto.GeneralPaperSourceInitializerTableStorage
open RationalOrderCell GeneralPaperProxyParameters GeneralPaperBasisStoredProducts
open GeneralPaperBasisState GeneralPaperBasisInvariant
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 8192

def window {T m : ℕ} (model : RationalCostModel) (W k outerCopied innerCopied : ℕ)
    (prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K) : ℕ :=
  GeneralPaperInitializerTableStorage.window model W outerCopied innerCopied inputs.controls.N inputs.controls.depth prep.dictionary.anchor

def AtBound {T m : ℕ} (model : RationalCostModel) (W k limit : ℕ) (b : ℝ) (reciprocal : Bool)
    (prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K)
    (state : State (m*((prepare m k).K-1)) (m*((prepare m k).K-1))) : Prop :=
  ∃ previousReserve roundingReserve,GeneralPaperSourceInitializerRoundingStorage.AtBound model W k previousReserve b reciprocal prep inputs state ∧
    (∀ j l,window model W k j l prep inputs≤roundingReserve) ∧ previousReserve+roundingReserve≤limit

theorem bound_mono {T m : ℕ} (model : RationalCostModel) (W k : ℕ) (b : ℝ) (reciprocal : Bool)
    (prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K)
    (state : State (m*((prepare m k).K-1)) (m*((prepare m k).K-1))) (B C : ℕ) (hBC : B≤C)
    (h : AtBound model W k B b reciprocal prep inputs state) : AtBound model W k C b reciprocal prep inputs state := by
  obtain ⟨D,F,hPrevious,hRounding,hSum⟩ := h
  exact ⟨D,F,hPrevious,hRounding,hSum.trans hBC⟩

theorem retained_rounding {T m : ℕ} (model : RationalCostModel) (W k limit : ℕ) (b : ℝ) (reciprocal : Bool)
    (prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K)
    (state : State (m*((prepare m k).K-1)) (m*((prepare m k).K-1)))
    (h : AtBound model W k limit b reciprocal prep inputs state) :
    ∀ j l outerCopied innerCopied,
      GeneralPaperSourceInitializerRoundingStorage.window model W k prep inputs j l+window model W k outerCopied innerCopied prep inputs≤limit := by
  obtain ⟨D,F,⟨D0,F0,_,hRounding,hOldSum⟩,hTable,hSum⟩ := h
  intro j l outerCopied innerCopied
  exact (Nat.add_le_add ((hRounding j l).trans (show F0≤D by omega)) (hTable outerCopied innerCopied)).trans hSum

theorem source_table {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv)
    (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool)
    (hW : 1≤W) (hK : binaryWordWidth ((prepare m k).K+1)≤W) (hM : binaryWordWidth (m+1)≤W) :
    let prep := GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b reciprocal
    let v := GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs
    let f := (GeneralPaperProxyClassifier.classify m k b).choice.proxy
    let inputs := GeneralPaperSharedBasisInputs.prepare k prep v f.num f.den reciprocal
    ∀ outerCopied innerCopied,window model W k outerCopied innerCopied prep inputs≤GeneralPaperSourceInitializerTableStorageRates.sourceProfile model W m k := by
  dsimp only
  intro outerCopied innerCopied
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
  have hHeight := GeneralPaperSourceScoreHeights.prepared_anchors k Qv hQv weights hp hs b hb reciprocal
  have hWidth : GeneralPaperInitializerRoundingBits.width (GeneralPaperSourceScoreHeights.anchorHeight m k)
      inputs.controls.N inputs.controls.depth≤GeneralPaperSourceInitializerTableStorageRates.operandWidth m k := by
    unfold GeneralPaperInitializerRoundingBits.width GeneralPaperSourceInitializerTableStorageRates.operandWidth
    dsimp only [G] at hGrid hDepth
    omega
  exact GeneralPaperInitializerTableStorage.bounded model W inputs.controls.N inputs.controls.depth
    (GeneralPaperSourceScoreHeights.anchorHeight m k) (GeneralPaperSourceInitializerTableStorageRates.operandWidth m k)
    outerCopied innerCopied hN hCap prep.dictionary.anchor (fun j l => ⟨hUnit.nonnegative j l,hUnit.bounded j l⟩) hHeight hWidth hW hK hM

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
      AtBound model W k (GeneralPaperSourceInitializerTableStorageRates.reservation model W m k) b reciprocal prep inputs state := by
  dsimp only
  intro state inv
  have hOld := GeneralPaperSourceInitializerRoundingStorage.source_stage model W k Qv hm hQv weights hp hs b hb reciprocal hModify hGuard
    hW hK hM hIndex hDim hBatch hFinalIndex state inv
  exact ⟨GeneralPaperSourceInitializerRoundingStorageRates.reservation model W m k,
    GeneralPaperSourceInitializerTableStorageRates.sourceProfile model W m k,hOld,
    source_table model W k Qv hm hQv weights hp hs b hb reciprocal hW hK hM,le_rfl⟩

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
      AtBound model W k (GeneralPaperSourceInitializerTableStorageRates.reservation model W m k) b reciprocal prep inputs state := by
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

end Blotto.GeneralPaperSourceInitializerTableStorage
