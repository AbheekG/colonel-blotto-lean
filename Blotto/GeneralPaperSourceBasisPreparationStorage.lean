import Blotto.GeneralPaperSourceBasisPreparationStorageRates

/-! Full actual reached-source point/direction preparation storage. Prefix
division, both assembly branches and enclosing solve/preparation returns
join the preceding retained basis/grid/RHS/integer-product windows. Native
source invariants derive all heights and prices; no return/size oracle. -/
namespace Blotto.GeneralPaperSourceBasisPreparationStorage
open RationalOrderCell GeneralPaperProxyParameters GeneralPaperBasisStoredProducts
open GeneralPaperBasisState GeneralPaperBasisInvariant GeneralPaperBasisOriginalDirection
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 8192

def window {T m j : ℕ} (model : RationalCostModel) (W k copied : ℕ)
    (_prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K)
    (state : State j (m*((prepare m k).K-1))) (hj : j<m*((prepare m k).K-1)) : ℕ :=
  let rhs := GeneralPaperBasisRHSBits.run model.rat W inputs.controls.N inputs.betaN state.rows inputs.initialGrid
  let column := GeneralPaperBasisAssemblyBits.columnRun W state.rows (next hj)
  let pointNumerators := GeneralPaperBasisProductBits.mulVecRun model.rat W state.adjugate rhs.1
  let directionNumerators := GeneralPaperBasisProductBits.mulVecRun model.rat W state.adjugate column.1
  let pointFirst := GeneralPaperBasisSolveBits.run model.rat W inputs.controls.N state.determinant state.adjugate rhs.1
  let directionFirst := GeneralPaperBasisSolveBits.run model.rat W 1 state.determinant state.adjugate column.1
  GeneralPaperBasisDivideStorage.window model W copied inputs.controls.N state.determinant pointNumerators.1+
    GeneralPaperBasisDivideStorage.window model W copied 1 state.determinant directionNumerators.1+
    GeneralPaperBasisAssemblyStorage.pointWindow model W copied inputs.controls.N pointFirst.values inputs.initialGrid+
    GeneralPaperBasisAssemblyStorage.directionWindow (d:=m*((prepare m k).K-1)) model W copied directionFirst.values+
    GeneralPaperBasisPreparationReturnStorage.solveWindow model W inputs.controls.N state.determinant state.adjugate rhs.1+
    GeneralPaperBasisPreparationReturnStorage.solveWindow model W 1 state.determinant state.adjugate column.1+
    GeneralPaperBasisPreparationReturnStorage.pointWindow model W inputs.controls.N inputs.betaN state.determinant state.adjugate state.rows inputs.initialGrid+
    GeneralPaperBasisPreparationReturnStorage.directionWindow model W state.determinant state.adjugate state.rows (next hj)

def StageAtBound {T m j : ℕ} (model : RationalCostModel) (W k limit : ℕ)
    (prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K)
    (state : State j (m*((prepare m k).K-1))) (hj : j<m*((prepare m k).K-1)) : Prop :=
  ∃ previousReserve preparationReserve,
    GeneralPaperSourceBasisRHSProductStorage.StageAtBound model W k previousReserve prep inputs state hj ∧
      (∀ copied,window model W k copied prep inputs state hj≤preparationReserve) ∧ previousReserve+preparationReserve≤limit

theorem stage_mono {T m j : ℕ} (model : RationalCostModel) (W k : ℕ)
    (prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K)
    (state : State j (m*((prepare m k).K-1))) (hj : j<m*((prepare m k).K-1)) (B C : ℕ) (hBC : B≤C)
    (h : StageAtBound model W k B prep inputs state hj) : StageAtBound model W k C prep inputs state hj := by
  obtain ⟨D,F,hPrevious,hPreparation,hSum⟩ := h
  exact ⟨D,F,hPrevious,hPreparation,hSum.trans hBC⟩

theorem simultaneous {T m j : ℕ} (model : RationalCostModel) (W k limit : ℕ)
    (prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K)
    (state : State j (m*((prepare m k).K-1))) (hj : j<m*((prepare m k).K-1))
    (hc : StageAtBound model W k limit prep inputs state hj) :
    ∃ previousReserve,
      GeneralPaperSourceBasisRHSProductStorage.StageAtBound model W k previousReserve prep inputs state hj ∧
      ∀ copied B,B≤previousReserve → B+window model W k copied prep inputs state hj≤limit := by
  obtain ⟨D,F,hPrevious,hPreparation,hSum⟩ := hc
  exact ⟨D,hPrevious,fun copied B hB => (Nat.add_le_add hB (hPreparation copied)).trans hSum⟩

theorem retained_products {T m j : ℕ} (model : RationalCostModel) (W k limit : ℕ)
    (prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K)
    (state : State j (m*((prepare m k).K-1))) (hj : j<m*((prepare m k).K-1))
    (hc : StageAtBound model W k limit prep inputs state hj) :
    ∀ oldCopied copied,GeneralPaperSourceBasisRHSProductStorage.window model W k oldCopied prep inputs state hj+
      window model W k copied prep inputs state hj≤limit := by
  obtain ⟨D,F,hPrevious,hPreparation,hSum⟩ := hc
  obtain ⟨D0,F0,_,hProducts,hOldSum⟩ := hPrevious
  intro oldCopied copied
  have hOld := (hProducts oldCopied).trans (show F0≤D by omega)
  exact (Nat.add_le_add hOld (hPreparation copied)).trans hSum

theorem source_stage {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv)
    (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool)
    (hW : 1≤W) (hK : binaryWordWidth ((prepare m k).K+1)≤W) (hM : binaryWordWidth (m+1)≤W)
    (hIndex : binaryWordWidth ((prepare m k).S+2)≤W) (hDim : binaryWordWidth (m*((prepare m k).K-1)+1)≤W)
    (hBatch : binaryWordWidth (((prepare m k).S+1)*((prepare m k).K*(prepare m k).K)+3)≤W)
    (hFinalIndex : binaryWordWidth ((prepare m k).S+4)≤W) :
    let prep := GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b reciprocal
    let v := GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs
    let f := (GeneralPaperProxyClassifier.classify m k b).choice.proxy
    let inputs := GeneralPaperSharedBasisInputs.prepare k prep v f.num f.den reciprocal
    ∀ j (hj : j<m*((prepare m k).K-1)) (state : State j (m*((prepare m k).K-1))),
      Invariant prep.dictionary v (prepare m k).S prep.threshold inputs.controls.N inputs.betaN inputs.initialGrid (Nat.le_of_lt hj) state →
      StageAtBound model W k (GeneralPaperSourceBasisPreparationStorageRates.reservation model W m k) prep inputs state hj := by
  dsimp only
  intro j hj state inv
  let prep := GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b reciprocal
  let v := GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs
  let f := (GeneralPaperProxyClassifier.classify m k b).choice.proxy
  let inputs := GeneralPaperSharedBasisInputs.prepare k prep v f.num f.den reciprocal
  let dim := m*((prepare m k).K-1)
  let C := m+1
  let H := (prepare m k).H
  let B := GeneralPaperSourceBasisGridSize.auxiliaryBound m k
  let R := GeneralPaperSourceBasisPreparationStorageRates.operandWidth m k
  let rhs := GeneralPaperBasisRHSBits.run model.rat W inputs.controls.N inputs.betaN state.rows inputs.initialGrid
  let column := GeneralPaperBasisAssemblyBits.columnRun W state.rows (next hj)
  have hOld := GeneralPaperSourceBasisRHSProductStorage.source_stage model W k Qv hm hQv weights hp hs b hb reciprocal
    hW hK hM hIndex hDim hBatch hFinalIndex j hj state inv
  have hCache := GeneralPaperBasisCacheSize.cache_H k hm prep.dictionary v (prepare m k).S prep.threshold inputs.controls.N
    inputs.betaN inputs.initialGrid (Nat.le_of_lt hj) state inv
  have hConstant (i) : (state.rows.read i).constant.natAbs≤C :=
    GeneralPaperBasisRowSize.rhs_entry hm prep.dictionary v (prepare m k).S prep.threshold inputs.controls.N inputs.betaN inputs.initialGrid
      (Nat.le_of_lt hj) state inv i false
  have hSlope (i) : (state.rows.read i).slope.natAbs≤C :=
    GeneralPaperBasisRowSize.rhs_entry hm prep.dictionary v (prepare m k).S prep.threshold inputs.controls.N inputs.betaN inputs.initialGrid
      (Nat.le_of_lt hj) state inv i true
  have hRows := GeneralPaperBasisRowSize.coefficient hm prep.dictionary v (prepare m k).S prep.threshold inputs.controls.N inputs.betaN inputs.initialGrid
    (Nat.le_of_lt hj) state inv
  have hGrid := GeneralPaperSourceBasisGridSize.grid k Qv hm hQv weights hp hs b hb reciprocal
  have hBeta := GeneralPaperSourceBasisGridSize.auxiliary (m:=m) k b hb reciprocal
  have hGridWord := GeneralPaperSourceRayStorageWidth.grid_bound m k b hb reciprocal
  change binaryWordWidth inputs.controls.N≤GeneralPaperSourceRayStorageWidth.gridWord m k at hGridWord
  have hEnvelope := GeneralPaperSourceBasisRHSProductStorage.operand_envelope m k inputs.controls.N hGridWord
  have hComponents := GeneralPaperBasisPreparationWidths.component_widths j dim C inputs.controls.N H B (Nat.le_of_lt hj)
  have hPoint := GeneralPaperBasisPreparationBits.point_component_widths j dim C inputs.controls.N H B
  let pointNumerators := GeneralPaperBasisProductBits.mulVecRun model.rat W state.adjugate rhs.1
  let directionNumerators := GeneralPaperBasisProductBits.mulVecRun model.rat W state.adjugate column.1
  let pointFirst := GeneralPaperBasisSolveBits.run model.rat W inputs.controls.N state.determinant state.adjugate rhs.1
  let directionFirst := GeneralPaperBasisSolveBits.run model.rat W 1 state.determinant state.adjugate column.1
  let sP := GeneralPaperBasisDivideBits.height inputs.controls.N H (j*H*(GeneralPaperBasisRHSBits.bound dim C inputs.controls.N B))
  let sD := GeneralPaperBasisDivideBits.height 1 H (j*H*C)
  have hPointWidth : GeneralPaperBasisPreparationBits.pointWidth j dim C inputs.controls.N H B≤R := hComponents.1.trans hEnvelope
  have hDirectionWidth : GeneralPaperBasisSolveBits.width j 1 H C≤R := hComponents.2.trans hEnvelope
  have hSolveWidth := hPoint.2.1.trans hPointWidth
  have hPointWord := (GeneralPaperBasisSolveBits.component_widths j inputs.controls.N H (GeneralPaperBasisRHSBits.bound dim C inputs.controls.N B)).2.trans hSolveWidth
  have hDirectionWord := (GeneralPaperBasisSolveBits.component_widths j 1 H C).2.trans hDirectionWidth
  have hTailWord := hPoint.2.2.trans hPointWidth
  have hJ : binaryWordWidth (j+1)≤W := (binaryWordWidth_mono (show j+1≤dim+1 by omega)).trans hDim
  have hRhsValue (i) : (rhs.1.read i).natAbs≤GeneralPaperBasisRHSBits.bound dim C inputs.controls.N B := by
    simp only [rhs,GeneralPaperBasisRHSBits.run,PaperIndexedArrayConstruction.run_data,FixedArrayTable.read_ofFn]
    exact GeneralPaperBasisRHSBits.scalar_bound model.rat W C inputs.controls.N B inputs.betaN j (state.rows.read i) inputs.initialGrid
      hBeta (hConstant i) (hSlope i) (hRows i) hGrid
  have hColumnValue (i) : (column.1.read i).natAbs≤C := by
    rw [GeneralPaperBasisAssemblyBits.column_data,GeneralPaperBasisDirection.column_read]; exact hRows i (next hj)
  have hPointNum (i) : (pointNumerators.1.read i).natAbs≤j*H*(GeneralPaperBasisRHSBits.bound dim C inputs.controls.N B) := by
    rw [GeneralPaperBasisProductBits.mulVec_data]
    exact GeneralPaperStoredProductSize.mulVec state.adjugate rhs.1 H _ hCache.2 hRhsValue i
  have hDirectionNum (i) : (directionNumerators.1.read i).natAbs≤j*H*C := by
    rw [GeneralPaperBasisProductBits.mulVec_data]
    exact GeneralPaperStoredProductSize.mulVec state.adjugate column.1 H C hCache.2 hColumnValue i
  have hPointPrefix (i) : RationalHeight (pointFirst.values.read i) sP :=
    GeneralPaperBasisSolveBits.result_height model.rat W inputs.controls.N H _ state.determinant state.adjugate rhs.1 hCache.1 hCache.2 hRhsValue i
  have hDirectionPrefix (i) : RationalHeight (directionFirst.values.read i) sD :=
    GeneralPaperBasisSolveBits.result_height model.rat W 1 H C state.determinant state.adjugate column.1 hCache.1 hCache.2 hColumnValue i
  have hsD : 1≤sD := by have h := binaryWordWidth_pos 1; unfold sD GeneralPaperBasisDivideBits.height; omega
  refine ⟨GeneralPaperSourceBasisRHSProductRates.reservation model W m k,
    GeneralPaperSourceBasisPreparationStorageRates.sourceProfile model W m k,hOld,?_,le_rfl⟩
  intro copied
  have hDP := GeneralPaperBasisDivideStorage.bounded model W copied inputs.controls.N H _ R state.determinant pointNumerators.1 hCache.1 hPointNum hPointWord hW hJ
  have hDD := GeneralPaperBasisDivideStorage.bounded model W copied 1 H _ R state.determinant directionNumerators.1 hCache.1 hDirectionNum hDirectionWord hW hJ
  have hAP := GeneralPaperBasisAssemblyStorage.point_bound model W copied inputs.controls.N R pointFirst.values inputs.initialGrid
    (fun i => (rationalWordWidth_of_height (hPointPrefix i)).trans hPointWord) hGrid hTailWord hW hDim
  have hAD := GeneralPaperBasisAssemblyStorage.direction_bound (d:=dim) model W copied sD R hsD directionFirst.values hDirectionPrefix hDirectionWord hW hDim
  have hSP := GeneralPaperBasisPreparationReturnStorage.solve_bound model W inputs.controls.N H _ R state.determinant state.adjugate rhs.1 hCache.1 hCache.2 hRhsValue hSolveWidth hW hJ
  have hSD := GeneralPaperBasisPreparationReturnStorage.solve_bound model W 1 H C R state.determinant state.adjugate column.1 hCache.1 hCache.2 hColumnValue hDirectionWidth hW hJ
  have hPP := GeneralPaperBasisPreparationReturnStorage.point_bound model W C inputs.controls.N H B R inputs.betaN state.determinant state.adjugate state.rows inputs.initialGrid
    hBeta hCache.1 hCache.2 hConstant hSlope hRows hGrid hPointWidth hW hJ hDim
  have hPD := GeneralPaperBasisPreparationReturnStorage.direction_bound model W C H R state.determinant state.adjugate state.rows (next hj)
    hCache.1 hCache.2 hRows hDirectionWidth hW hJ hDim
  have hNative : window model W k copied prep inputs state hj≤GeneralPaperSourceBasisPreparationStorageRates.profile model W j dim R := by
    unfold window GeneralPaperSourceBasisPreparationStorageRates.profile
    dsimp only
    dsimp only [pointNumerators,directionNumerators,pointFirst,directionFirst,rhs,column] at hDP hDD hAP hAD hSP hSD
    dsimp only [dim] at hAP hAD hPP hPD ⊢
    omega
  exact hNative.trans (GeneralPaperSourceBasisPreparationStorageRates.dimensions_mono model W j dim dim R (Nat.le_of_lt hj) le_rfl)

theorem actual_reached {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv)
    (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool)
    (hW : 1≤W) (hK : binaryWordWidth ((prepare m k).K+1)≤W) (hM : binaryWordWidth (m+1)≤W)
    (hIndex : binaryWordWidth ((prepare m k).S+2)≤W) (hDim : binaryWordWidth (m*((prepare m k).K-1)+1)≤W)
    (hBatch : binaryWordWidth (((prepare m k).S+1)*((prepare m k).K*(prepare m k).K)+3)≤W)
    (hFinalIndex : binaryWordWidth ((prepare m k).S+4)≤W)
    (j : ℕ) (hj : j<m*((prepare m k).K-1)) :
    let prep := GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b reciprocal
    let v := GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs
    let f := (GeneralPaperProxyClassifier.classify m k b).choice.proxy
    let inputs := GeneralPaperSharedBasisInputs.prepare k prep v f.num f.den reciprocal
    ∃ state,(GeneralPaperBasisControllerBits.stages model W prep.dictionary.label inputs.matrix (prepare m k).S prep.threshold
      inputs.controls.N inputs.betaN inputs.initialGrid j (Nat.le_of_lt hj)).1=some state ∧
      StageAtBound model W k (GeneralPaperSourceBasisPreparationStorageRates.reservation model W m k) prep inputs state hj := by
  let prep := GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b reciprocal
  let v := GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs
  let f := (GeneralPaperProxyClassifier.classify m k b).choice.proxy
  let inputs := GeneralPaperSharedBasisInputs.prepare k prep v f.num f.den reciprocal
  have hStart := GeneralPaperSourceBasisInputValidity.actual_start k Qv hm hQv weights hp hs b hb reciprocal
  have hN : 0 < inputs.controls.N := (GeneralPaperInitializerSelectedControls.positive m k hm b hb reciprocal).1
  obtain ⟨state,hr,inv⟩ := GeneralPaperBasisControllerSound.stages_valid (GeneralPaperScoreScaleParameters.prepare m k).depth
    prep.dictionary v (GeneralPaperScoreScaleParameters.labels_positive m k) (prepare m k).S prep.threshold inputs.controls.N hN
    (GeneralPaperScoreScaleParameters.score_cap m k) inputs.betaN inputs.initialGrid hStart j (Nat.le_of_lt hj)
  have hReturn : GeneralPaperBasisController.stages prep.dictionary.label inputs.matrix (prepare m k).S prep.threshold
      inputs.controls.N inputs.betaN inputs.initialGrid j (Nat.le_of_lt hj)=some state := by rw [GeneralPaperSharedBasisInputs.matrix_eq]; exact hr
  refine ⟨state,?_,source_stage model W k Qv hm hQv weights hp hs b hb reciprocal hW hK hM hIndex hDim hBatch hFinalIndex j hj state inv⟩
  exact (GeneralPaperBasisControllerBits.stages_data model W _ _ _ _ _ _ _ _ _).trans hReturn

end Blotto.GeneralPaperSourceBasisPreparationStorage
