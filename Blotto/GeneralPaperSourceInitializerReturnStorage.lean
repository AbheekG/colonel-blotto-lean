import Blotto.GeneralPaperSourceInitializerReturnStorageRates

/-! Actual grid/input parent returns. Native source identities derive
complete table/grid/control/matrix ownership and uniform actual grid/input
work bounds. All earlier packing/constructor/scalar/controller/stage/source
reserves remain. Prepared dictionary/label owners remain shared with the
still-open enclosing source phase. -/
namespace Blotto.GeneralPaperSourceInitializerReturnStorage
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
  GeneralPaperInitializerGridReturnStorage.window model W inputs.controls.N inputs.controls.depth prep.dictionary+
    GeneralPaperRetainedInputsReturnStorage.window model W (prepare m k).H f.num f.den reciprocal prep inputs.matrix

def AtBound {T m : ℕ} (model : RationalCostModel) (W k limit : ℕ) (b : ℝ) (reciprocal : Bool)
    (prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K)
    (state : State (m*((prepare m k).K-1)) (m*((prepare m k).K-1))) : Prop :=
  ∃ previousReserve returnReserve,GeneralPaperSourceBasisGridPackingStorage.AtBound model W k previousReserve b reciprocal prep inputs state ∧
    window model W k b reciprocal prep inputs≤returnReserve ∧ previousReserve+returnReserve≤limit

theorem bound_mono {T m : ℕ} (model : RationalCostModel) (W k : ℕ) (b : ℝ) (reciprocal : Bool)
    (prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K)
    (state : State (m*((prepare m k).K-1)) (m*((prepare m k).K-1))) (B C : ℕ) (hBC : B≤C)
    (h : AtBound model W k B b reciprocal prep inputs state) : AtBound model W k C b reciprocal prep inputs state := by
  obtain ⟨D,F,hPrevious,hReturns,hSum⟩ := h
  exact ⟨D,F,hPrevious,hReturns,hSum.trans hBC⟩

theorem retained_packing {T m : ℕ} (model : RationalCostModel) (W k limit : ℕ) (b : ℝ) (reciprocal : Bool)
    (prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K)
    (state : State (m*((prepare m k).K-1)) (m*((prepare m k).K-1)))
    (h : AtBound model W k limit b reciprocal prep inputs state) :
    ∀ z e af al,GeneralPaperSourceBasisGridPackingStorage.window model W k z e prep inputs af al+
      window model W k b reciprocal prep inputs≤limit := by
  obtain ⟨D,F,⟨D0,F0,_,hPacking,hOldSum⟩,hReturns,hSum⟩ := h
  intro z e af al
  exact (Nat.add_le_add ((hPacking z e af al).trans (show F0≤D by omega)) hReturns).trans hSum

theorem source_returns {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv)
    (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool) (hW : 1≤W)
    (hK : binaryWordWidth ((prepare m k).K+1)≤W) (hM : binaryWordWidth (m+1)≤W)
    (hD : binaryWordWidth (m*((prepare m k).K-1)+1)≤W) :
    let prep := GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b reciprocal
    let v := GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs
    let f := (GeneralPaperProxyClassifier.classify m k b).choice.proxy
    let inputs := GeneralPaperSharedBasisInputs.prepare k prep v f.num f.den reciprocal
    window model W k b reciprocal prep inputs≤GeneralPaperSourceInitializerReturnStorageRates.sourceProfile model W m k ∧
      (GeneralPaperRetainedBasisInputs.run true model W (prepare m k).H f.num f.den reciprocal prep inputs.matrix).2≤
        GeneralPaperSourceInitializerReturnStorageRates.inputPrice model W m k ∧
      (GeneralPaperInitializerGridPrice.run model W inputs.controls.N inputs.controls.depth prep.dictionary).2≤
        GeneralPaperSourceInitializerReturnStorageRates.gridPrice model W m k := by
  dsimp only
  let prep := GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b reciprocal
  let v := GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs
  let f := (GeneralPaperProxyClassifier.classify m k b).choice.proxy
  let inputs := GeneralPaperSharedBasisInputs.prepare k prep v f.num f.den reciprocal
  let G := GeneralPaperSourceRayStorageWidth.gridWord m k
  let R := GeneralPaperSourceInitializerTableStorageRates.operandWidth m k
  let P := GeneralPaperSourceBasisGridPackingStorageRates.operandWidth m k
  let C := GeneralPaperSourceInitializerControlStorageRates.operandWidth m k
  let selected := GeneralPaperRetainedBasisInputs.controls true model W m (prepare m k).H f.num f.den reciprocal
  let initial := GeneralPaperRetainedBasisInputs.grid true model W selected.1.1.N selected.1.1.depth prep.dictionary
  have hSelected : selected.1=(inputs.controls,inputs.betaN) := GeneralPaperRetainedBasisInputs.controls_data true model W m (prepare m k).H f.num f.den reciprocal
  have hN : 0 < inputs.controls.N := (GeneralPaperInitializerSelectedControls.positive m k hm b hb reciprocal).1
  have hCap : inputs.controls.N<2^inputs.controls.depth := GeneralPaperInitializerParameters.quotient_cap m (prepare m k).H f.num f.den reciprocal
  have hGridWord := GeneralPaperSourceRayStorageWidth.grid_bound m k b hb reciprocal
  change binaryWordWidth inputs.controls.N≤G at hGridWord
  have hNWord : natBits inputs.controls.N≤P := Nat.add_le_add_left hGridWord 1
  have hDepth : inputs.controls.depth≤G+1 := by
    have h := GeneralPaperPowerCeiling.loop_depth inputs.controls.N 1 (by decide)
    change (GeneralPaperPowerCeiling.ceiling inputs.controls.N).doublings≤binaryWordWidth inputs.controls.N at h
    change (GeneralPaperPowerCeiling.ceiling inputs.controls.N).doublings+1≤G+1
    omega
  have hDepthR : inputs.controls.depth≤R := by unfold R GeneralPaperSourceInitializerTableStorageRates.operandWidth; dsimp only [G] at hDepth; omega
  have hUnit := GeneralPaperSourceUnchangedDictionary.unit k Qv hm hQv weights hp hs b hb reciprocal
  have hHeight := GeneralPaperSourceScoreHeights.prepared_anchors k Qv hQv weights hp hs b hb reciprocal
  have hWidth : GeneralPaperInitializerRoundingBits.width (GeneralPaperSourceScoreHeights.anchorHeight m k)
      inputs.controls.N inputs.controls.depth≤R := by
    unfold R GeneralPaperInitializerRoundingBits.width GeneralPaperSourceInitializerTableStorageRates.operandWidth
    dsimp only [G] at hGridWord hDepth
    omega
  have hTable : GeneralPaperInitializerGridReturnStorage.tableFoot W
      (GeneralPaperInitializerStoredBits.run model W inputs.controls.N inputs.controls.depth prep.dictionary.anchor).1≤
      GeneralPaperSourceInitializerReturnStorageRates.tableProfile W m k := by
    apply GeneralPaperEncodedBasisStorage.array_bound
    intro j
    apply GeneralPaperEncodedBasisStorage.array_bound
    intro l
    rw [GeneralPaperInitializerStoredBits.read_data]
    rw [←GeneralPaperInitializerRoundingBits.data model W inputs.controls.N inputs.controls.depth (prep.dictionary.anchor j l)]
    exact GeneralPaperInitializerTableStorage.entry_bound model W inputs.controls.N inputs.controls.depth
      (GeneralPaperSourceScoreHeights.anchorHeight m k) R hN hCap _ ⟨hUnit.nonnegative j l,hUnit.bounded j l⟩ hWidth
  have hNativeGrid : (GeneralPaperBasisGridPackingPrice.run (fun w => w) model.rat W
      (GeneralPaperInitializerGridPrice.values (GeneralPaperInitializerStoredBits.run model W inputs.controls.N inputs.controls.depth prep.dictionary.anchor).1)).1=inputs.initialGrid :=
    congrArg Prod.snd (GeneralPaperInitializerGridPrice.data model W inputs.controls.N inputs.controls.depth prep.dictionary hN)
  have hGridSize := GeneralPaperSourceBasisGridSize.grid k Qv hm hQv weights hp hs b hb reciprocal
  have hGridOwner : arrayFootprint W integerBits inputs.initialGrid≤GeneralPaperSourceInitializerReturnStorageRates.gridProfile W m k :=
    GeneralPaperEncodedBasisStorage.array_bound W P integerBits inputs.initialGrid (fun i =>
      (Nat.add_le_add_left (binaryWordWidth_mono (hGridSize i)) 1).trans hNWord)
  have hPackedOwner : arrayFootprint W integerBits (GeneralPaperBasisGridPackingPrice.run (fun w => w) model.rat W
      (GeneralPaperInitializerGridPrice.values (GeneralPaperInitializerStoredBits.run model W inputs.controls.N inputs.controls.depth prep.dictionary.anchor).1)).1≤
      GeneralPaperSourceInitializerReturnStorageRates.gridProfile W m k := by rw [hNativeGrid]; exact hGridOwner
  have hStoredWork := GeneralPaperInitializerStoredBits.work model W inputs.controls.N inputs.controls.depth
    (GeneralPaperSourceScoreHeights.anchorHeight m k) hN hCap prep.dictionary.anchor
    (fun j l => ⟨hUnit.nonnegative j l,hUnit.bounded j l⟩) hHeight hW hK hM
  have hStoredCap : (GeneralPaperInitializerStoredBits.run model W inputs.controls.N inputs.controls.depth prep.dictionary.anchor).2≤
      GeneralPaperSourceInitializerReturnStorageRates.storedPrice model W m k := by
    apply hStoredWork.trans
    unfold GeneralPaperInitializerStoredBits.profile GeneralPaperSourceInitializerReturnStorageRates.storedPrice
    dsimp only
    gcongr
    exact model.monotone hWidth
  have hPackedWork := GeneralPaperBasisGridPackingPrice.work model.rat model.monotone W inputs.controls.N
    (GeneralPaperInitializerGridPrice.values (GeneralPaperInitializerStoredBits.run model W inputs.controls.N inputs.controls.depth prep.dictionary.anchor).1)
    (GeneralPaperInitializerGridPrice.values_bound model W inputs.controls.N inputs.controls.depth prep.dictionary hN hCap
      (fun j l => ⟨hUnit.nonnegative j l,hUnit.bounded j l⟩)) hW hD
  have hPackedCap : (GeneralPaperBasisGridPackingPrice.run (fun w => w) model.rat W
      (GeneralPaperInitializerGridPrice.values (GeneralPaperInitializerStoredBits.run model W inputs.controls.N inputs.controls.depth prep.dictionary.anchor).1)).2≤
      GeneralPaperSourceInitializerReturnStorageRates.packedPrice model W m k := by
    apply hPackedWork.trans
    unfold GeneralPaperSourceInitializerReturnStorageRates.packedPrice GeneralPaperBasisGridPackingPrice.profile
    exact Nat.mul_le_mul_left _ (Nat.add_le_add_left (model.monotone hNWord) _)
  have hGridWork := GeneralPaperInitializerGridReturnStorage.work model W inputs.controls.N inputs.controls.depth _ _ prep.dictionary hStoredCap hPackedCap
  change _≤GeneralPaperSourceInitializerReturnStorageRates.gridPrice model W m k at hGridWork
  have hControlStorage := GeneralPaperSourceInitializerControlStorage.source_controls model W m k hm b hb reciprocal
  have hControlData : (GeneralPaperInitializerControlBits.run model W m (prepare m k).H f.num f.den reciprocal).1=(inputs.controls,inputs.betaN) :=
    (GeneralPaperInitializerControlBits.data model W m (prepare m k).H f.num f.den reciprocal).trans
      (GeneralPaperInitializerControlWork.data m (prepare m k).H f.num f.den reciprocal)
  have hArgs : natBits (prepare m k).H+natBits f.num+natBits f.den≤
      ((GeneralPaperInitializerControlScalarStorage.naturals m (prepare m k).H f.num f.den reciprocal).map natBits).sum := by
    simp only [GeneralPaperInitializerControlScalarStorage.naturals,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
    omega
  have hControlOwner : GeneralPaperRetainedInputsReturnStorage.controlFoot W (prepare m k).H f.num f.den selected.1≤
      GeneralPaperSourceInitializerControlStorageRates.sourceProfile model W m k := by
    change GeneralPaperInitializerControlStorage.window model W m (prepare m k).H f.num f.den reciprocal≤_ at hControlStorage
    unfold GeneralPaperInitializerControlStorage.window GeneralPaperInitializerControlScalarStorage.window at hControlStorage
    dsimp only at hControlStorage
    rw [hControlData] at hControlStorage
    rw [hSelected]
    unfold GeneralPaperRetainedInputsReturnStorage.controlFoot
    omega
  have hf := GeneralPaperProxyClassifier.proxy_integer_representation m k b hb
  have hControlWidth : GeneralPaperInitializerControlSize.width m (prepare m k).H f.num f.den≤C :=
    (GeneralPaperInitializerControlSize.positive_width m (prepare m k).H f.num f.den hm (H_positive m k) hf.1 f.den_pos).trans
      (Nat.add_le_add_left (Nat.mul_le_mul_left 64 hGridWord) 96)
  have hNControl : binaryWordWidth inputs.controls.N≤C := hGridWord.trans (by unfold C GeneralPaperSourceInitializerControlStorageRates.operandWidth; dsimp only [G]; omega)
  have hControlWork : selected.2≤GeneralPaperSourceInitializerReturnStorageRates.controlPrice model W m k := by
    have h := GeneralPaperInitializerControlBits.work model W m (prepare m k).H f.num f.den reciprocal
    exact h.trans (Nat.mul_le_mul (Nat.mul_le_mul_left 1024 (Nat.add_le_add_right hNControl 1)) (Nat.add_le_add_left (model.monotone hControlWidth) W))
  have hInitial : initial=GeneralPaperInitializerGridPrice.run model W inputs.controls.N inputs.controls.depth prep.dictionary := by
    dsimp only [initial]
    rw [hSelected]
    rfl
  have hInitialGrid : arrayFootprint W integerBits initial.1.2≤GeneralPaperSourceInitializerReturnStorageRates.gridProfile W m k := by
    rw [hInitial]
    exact hPackedOwner
  have hInitialWork : initial.2≤GeneralPaperSourceInitializerReturnStorageRates.gridPrice model W m k := by rw [hInitial]; exact hGridWork
  have hMatrix : GeneralPaperEncodedScoreMatrixStorage.matrixFootprint W inputs.matrix≤GeneralPaperSourceInitializerReturnStorageRates.matrixProfile W m k := by
    apply GeneralPaperEncodedScoreMatrixStorage.matrix_bound
    · intro j l
      rw [GeneralPaperSharedBasisInputs.matrix_eq]
      erw [GeneralPaperScoreMatrixWork.matrix_data (GeneralPaperScoreScaleParameters.prepare m k).depth prep.dictionary v
        (prepare m k).S (GeneralPaperScoreScaleParameters.labels_positive m k) (GeneralPaperScoreScaleParameters.score_cap m k)]
      simp only [FixedArrayTable.read_ofFn]
      convert GeneralPaperEncodedScoreMatrixStorage.score_bound v (prepare m k).S
        (GeneralPaperScoreScaleParameters.labels_positive m k) j l using 1
      rfl
    · intro j l
      rw [GeneralPaperSharedBasisInputs.matrix_eq]
      erw [GeneralPaperScoreMatrixWork.matrix_data (GeneralPaperScoreScaleParameters.prepare m k).depth prep.dictionary v
        (prepare m k).S (GeneralPaperScoreScaleParameters.labels_positive m k) (GeneralPaperScoreScaleParameters.score_cap m k)]
      simpa only [FixedArrayTable.read_ofFn] using hHeight j l
  have hGridReturn := GeneralPaperInitializerGridReturnStorage.bounded model W inputs.controls.N inputs.controls.depth
    _ _ P R _ _ prep.dictionary hTable hPackedOwner hNWord hDepthR hStoredCap hPackedCap
  have hInputReturn := GeneralPaperRetainedInputsReturnStorage.bounded model W (prepare m k).H f.num f.den
    _ _ _ _ _ reciprocal prep inputs.matrix hControlOwner hInitialGrid hMatrix hControlWork hInitialWork
  have hInputWork := GeneralPaperRetainedInputsReturnStorage.work model W (prepare m k).H f.num f.den _ _ reciprocal prep inputs.matrix hControlWork hInitialWork
  refine ⟨?_,hInputWork,hGridWork⟩
  exact Nat.add_le_add hGridReturn hInputReturn

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
      AtBound model W k (GeneralPaperSourceInitializerReturnStorageRates.reservation model W m k) b reciprocal prep inputs state := by
  dsimp only
  intro state inv
  have hOld := GeneralPaperSourceBasisGridPackingStorage.source_stage model W k Qv hm hQv weights hp hs b hb reciprocal hModify hGuard
    hW hK hM hIndex hDim hBatch hFinalIndex state inv
  have hDim1 := (binaryWordWidth_mono (show m*((prepare m k).K-1)+1≤m*((prepare m k).K-1)+3 by omega)).trans hDim
  exact ⟨GeneralPaperSourceBasisGridPackingStorageRates.reservation model W m k,
    GeneralPaperSourceInitializerReturnStorageRates.sourceProfile model W m k,hOld,
    (source_returns model W k Qv hm hQv weights hp hs b hb reciprocal hW hK hM hDim1).1,le_rfl⟩

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
      AtBound model W k (GeneralPaperSourceInitializerReturnStorageRates.reservation model W m k) b reciprocal prep inputs state := by
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

end Blotto.GeneralPaperSourceInitializerReturnStorage
