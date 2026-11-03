import Blotto.GeneralPaperSourceBasisRHSProductRates

/-! Actual reached-source fresh RHS and cached integer products. Full
basis state, fixed initial grid, original N/beta, RHS, point numerator,
direction column/numerator and native constructor windows coexist. Original
invariants and native width/return facts derive every bound. Rational divide,
assembly and complete preparation callers remain separate next joins. -/
namespace Blotto.GeneralPaperSourceBasisRHSProductStorage
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
  GeneralPaperEncodedBasisStorage.footprint W state+
    GeneralPaperEncodedBasisStorage.arrayFootprint W GeneralPaperEncodedBasisStorage.integerBits inputs.initialGrid+
    GeneralPaperEncodedScalarStorage.natBits inputs.controls.N+GeneralPaperEncodedBasisStorage.integerBits inputs.betaN+
    GeneralPaperBasisRHSStorage.window model W copied inputs.controls.N inputs.betaN state.rows inputs.initialGrid+
    GeneralPaperBasisProductStorage.window model W copied (fun i a => (state.adjugate.read i).read a) (fun _ => rhs.1.read)+
    GeneralPaperBasisProductStorage.columnWindow W copied state.rows (next hj)+
    GeneralPaperBasisProductStorage.window model W copied (fun i a => (state.adjugate.read i).read a) (fun _ => column.1.read)

def StageAtBound {T m j : ℕ} (model : RationalCostModel) (W k limit : ℕ)
    (prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K)
    (state : State j (m*((prepare m k).K-1))) (hj : j<m*((prepare m k).K-1)) : Prop :=
  ∃ previousReserve preparationReserve,
    GeneralPaperSourceBasisDenseConstructionStorage.StageAtBound model W k previousReserve prep inputs state hj ∧
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
      GeneralPaperSourceBasisDenseConstructionStorage.StageAtBound model W k previousReserve prep inputs state hj ∧
      ∀ copied B,B≤previousReserve → B+window model W k copied prep inputs state hj≤limit := by
  obtain ⟨D,F,hPrevious,hPreparation,hSum⟩ := hc
  exact ⟨D,hPrevious,fun copied B hB => (Nat.add_le_add hB (hPreparation copied)).trans hSum⟩

theorem operand_envelope (m k N : ℕ) (hN : binaryWordWidth N≤GeneralPaperSourceRayStorageWidth.gridWord m k) :
    GeneralPaperBasisPreparationWidths.envelope (m*((prepare m k).K-1)) (m+1) N (prepare m k).H
      (GeneralPaperSourceBasisGridSize.auxiliaryBound m k)≤GeneralPaperSourceBasisRHSProductRates.operandWidth m k := by
  have h := GeneralPaperBasisPreparationWidths.paper_envelope m k N (prepare m k).S
    (GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows
  unfold GeneralPaperSourceBasisRHSProductRates.operandWidth GeneralPaperSourceRayStorageWidth.width GeneralPaperSourceRayStorageWidth.rootWidth
  ring_nf at h ⊢
  omega

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
      StageAtBound model W k (GeneralPaperSourceBasisRHSProductRates.reservation model W m k) prep inputs state hj := by
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
  let R := GeneralPaperSourceBasisRHSProductRates.operandWidth m k
  let rhs := GeneralPaperBasisRHSBits.run model.rat W inputs.controls.N inputs.betaN state.rows inputs.initialGrid
  let column := GeneralPaperBasisAssemblyBits.columnRun W state.rows (next hj)
  have hOld := GeneralPaperSourceBasisDenseConstructionStorage.source_stage model W k Qv hm hQv weights hp hs b hb reciprocal
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
  have hEnvelope := operand_envelope m k inputs.controls.N hGridWord
  have hComponents := GeneralPaperBasisPreparationWidths.component_widths j dim C inputs.controls.N H B (Nat.le_of_lt hj)
  have hPoint := GeneralPaperBasisPreparationBits.point_component_widths j dim C inputs.controls.N H B
  have hRHSWidth : GeneralPaperBasisRHSBits.width dim C inputs.controls.N B≤R := hPoint.1.trans (hComponents.1.trans hEnvelope)
  have hPointWord : 1+binaryWordWidth (GeneralPaperIntegerDotPrice.cap j H (GeneralPaperBasisRHSBits.bound dim C inputs.controls.N B))≤R :=
    (GeneralPaperBasisSolveBits.component_widths j inputs.controls.N H (GeneralPaperBasisRHSBits.bound dim C inputs.controls.N B)).1.trans
      (hPoint.2.1.trans (hComponents.1.trans hEnvelope))
  have hDirectionWord : 1+binaryWordWidth (GeneralPaperIntegerDotPrice.cap j H C)≤R :=
    (GeneralPaperBasisSolveBits.component_widths j 1 H C).1.trans (hComponents.2.trans hEnvelope)
  have hCWord : 1+binaryWordWidth C≤R := (Nat.add_le_add_left
    (binaryWordWidth_mono (GeneralPaperIntegerDotPrice.cap_bounds j H C).2.1) 1).trans hDirectionWord
  have hCoreWord : 1+binaryWordWidth (GeneralPaperBasisRHSBits.coreCap dim C inputs.controls.N B)≤R := by
    unfold GeneralPaperBasisRHSBits.width at hRHSWidth; omega
  have hNWord : GeneralPaperEncodedScalarStorage.natBits inputs.controls.N≤R :=
    (Nat.add_le_add_left (binaryWordWidth_mono (show inputs.controls.N≤GeneralPaperBasisRHSBits.coreCap dim C inputs.controls.N B by unfold GeneralPaperBasisRHSBits.coreCap; omega)) 1).trans hCoreWord
  have hBetaWord : GeneralPaperEncodedBasisStorage.integerBits inputs.betaN≤R :=
    (Nat.add_le_add_left (binaryWordWidth_mono ((show inputs.betaN.natAbs≤B from hBeta).trans
      (show B≤GeneralPaperBasisRHSBits.coreCap dim C inputs.controls.N B by unfold GeneralPaperBasisRHSBits.coreCap; omega))) 1).trans hCoreWord
  have hInitial := GeneralPaperEncodedBasisStorage.array_bound W R GeneralPaperEncodedBasisStorage.integerBits inputs.initialGrid
    (fun i => (Nat.add_le_add_left (binaryWordWidth_mono (hGrid i)) 1).trans hNWord)
  have hBasis := GeneralPaperEncodedBasisStorage.invariant_bound W k hm prep.dictionary v (prepare m k).S prep.threshold inputs.controls.N inputs.betaN
    inputs.initialGrid (Nat.le_of_lt hj) state inv
  have hJ : binaryWordWidth (j+1)≤W := (binaryWordWidth_mono (show j+1≤dim+1 by omega)).trans hDim
  have hRhsValue (i) : (rhs.1.read i).natAbs≤GeneralPaperBasisRHSBits.bound dim C inputs.controls.N B := by
    simp only [rhs,GeneralPaperBasisRHSBits.run,PaperIndexedArrayConstruction.run_data,FixedArrayTable.read_ofFn]
    exact GeneralPaperBasisRHSBits.scalar_bound model.rat W C inputs.controls.N B inputs.betaN j (state.rows.read i) inputs.initialGrid
      hBeta (hConstant i) (hSlope i) (hRows i) hGrid
  have hColumnValue (i) : (column.1.read i).natAbs≤C := by
    rw [GeneralPaperBasisAssemblyBits.column_data,GeneralPaperBasisDirection.column_read]
    exact hRows i (next hj)
  refine ⟨GeneralPaperSourceBasisDenseConstructionRates.reservation model W m k,
    GeneralPaperSourceBasisRHSProductRates.sourceProfile model W m k,hOld,?_,le_rfl⟩
  intro copied
  have hRhs := GeneralPaperBasisRHSStorage.bounded model W copied C inputs.controls.N B R inputs.betaN state.rows inputs.initialGrid
    (Nat.le_of_lt hj) hBeta hConstant hSlope hRows hGrid hRHSWidth hW hJ
  have hProduct := GeneralPaperBasisProductStorage.bounded model W copied H (GeneralPaperBasisRHSBits.bound dim C inputs.controls.N B) R
    (fun i a => (state.adjugate.read i).read a) (fun _ => rhs.1.read) hCache.2 (fun _ i => hRhsValue i) hPointWord hW hJ
  have hColumn := GeneralPaperBasisProductStorage.column_bound W copied C R state.rows (next hj) hRows hCWord hW hJ
  have hDirection := GeneralPaperBasisProductStorage.bounded model W copied H C R
    (fun i a => (state.adjugate.read i).read a) (fun _ => column.1.read) hCache.2 (fun _ i => hColumnValue i) hDirectionWord hW hJ
  have hNative : window model W k copied prep inputs state hj≤GeneralPaperEncodedBasisStorage.paperProfile W m k+
      GeneralPaperSourceBasisRHSProductRates.profile model W j dim R := by
    unfold window GeneralPaperSourceBasisRHSProductRates.profile
    dsimp only
    dsimp only [rhs,column] at hProduct hDirection
    dsimp only [dim] at hInitial hRhs hColumn ⊢
    omega
  have hDimensions := GeneralPaperSourceBasisRHSProductRates.dimensions_mono model W j dim dim R (Nat.le_of_lt hj) le_rfl
  apply hNative.trans
  change GeneralPaperEncodedBasisStorage.paperProfile W m k+GeneralPaperSourceBasisRHSProductRates.profile model W j dim R≤
    GeneralPaperSourceBasisRHSProductRates.profile model W dim dim R+GeneralPaperEncodedBasisStorage.paperProfile W m k
  omega

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
      StageAtBound model W k (GeneralPaperSourceBasisRHSProductRates.reservation model W m k) prep inputs state hj := by
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

end Blotto.GeneralPaperSourceBasisRHSProductStorage
