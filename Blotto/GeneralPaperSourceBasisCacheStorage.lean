import Blotto.GeneralPaperSourceBasisCacheStorageRates

/-! The actual native endpoint supplies the blocker for the complete
bordered cache update. Original invariants derive every size, validity and
exact-division premise. Budget creation and the new cache coexist with all
preceding preparation, basis/grid and ray-return construction reserves. -/
namespace Blotto.GeneralPaperSourceBasisCacheStorage
open RationalOrderCell GeneralPaperProxyParameters GeneralPaperBasisStoredProducts
open GeneralPaperBasisState GeneralPaperBasisInvariant GeneralPaperBasisOriginalDirection
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 8192

def cacheWindow {T m K j : ℕ} (model : RationalCostModel) (W copied outerCopied innerCopied : ℕ)
    (labels : Fin T → Fin m → Fin K) (state : State j (m*(K-1))) (hj : j<m*(K-1))
    (answer : GeneralPaperRayEndpoint.Answer T m K) : ℕ :=
  let original := GeneralPaperBlockerRowPrice.run W labels answer.blocker
  let dense := GeneralPaperBasisDenseBits.run model.rat W original.1
  let u := GeneralPaperBasisAssemblyBits.columnRun W state.rows (next hj)
  let p := GeneralPaperBasisArrayPrice.prefixRun (fun w => w) W dense.1 (Nat.le_of_lt hj)
  GeneralPaperBasisCacheStorage.window model W copied outerCopied innerCopied state.determinant state.adjugate
    u.1 p.1 (dense.1.coefficients.read (next hj))

def endpoint {T m j : ℕ} (model : RationalCostModel) (W k : ℕ)
    (prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K)
    (state : State j (m*((prepare m k).K-1))) (hj : j<m*((prepare m k).K-1)) :=
  let point := GeneralPaperBasisPreparationBits.point model.rat W inputs.controls.N inputs.betaN state.determinant state.adjugate state.rows inputs.initialGrid
  let velocity := GeneralPaperBasisPreparationBits.direction model.rat W state.determinant state.adjugate state.rows (next hj)
  let budget := GeneralPaperBasisBudgetBits.run model.rat W inputs.controls.N inputs.betaN
  GeneralPaperEndpointBits.run model W prep.dictionary.label inputs.matrix (prepare m k).S prep.threshold budget.1 (reader point.point) (reader velocity.velocity)

def window {T m j : ℕ} (model : RationalCostModel) (W k copied outerCopied innerCopied : ℕ)
    (prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K)
    (state : State j (m*((prepare m k).K-1))) (hj : j<m*((prepare m k).K-1))
    (answer : GeneralPaperRayEndpoint.Answer T m (prepare m k).K) : ℕ :=
  GeneralPaperBasisBudgetStorage.window model W inputs.controls.N inputs.betaN+
    cacheWindow model W copied outerCopied innerCopied prep.dictionary.label state hj answer

def StageAtBound {T m j : ℕ} (model : RationalCostModel) (W k limit : ℕ)
    (prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K)
    (state : State j (m*((prepare m k).K-1))) (hj : j<m*((prepare m k).K-1)) : Prop :=
  ∃ previousReserve cacheReserve,
    GeneralPaperSourceBasisPreparationStorage.StageAtBound model W k previousReserve prep inputs state hj ∧
      (∃ answer,(endpoint model W k prep inputs state hj).1=some answer ∧
        ∀ copied outerCopied innerCopied,window model W k copied outerCopied innerCopied prep inputs state hj answer≤cacheReserve) ∧
      previousReserve+cacheReserve≤limit

theorem stage_mono {T m j : ℕ} (model : RationalCostModel) (W k : ℕ)
    (prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K)
    (state : State j (m*((prepare m k).K-1))) (hj : j<m*((prepare m k).K-1)) (B C : ℕ) (hBC : B≤C)
    (h : StageAtBound model W k B prep inputs state hj) : StageAtBound model W k C prep inputs state hj := by
  obtain ⟨D,F,hPrevious,hCache,hSum⟩ := h
  exact ⟨D,F,hPrevious,hCache,hSum.trans hBC⟩

theorem simultaneous {T m j : ℕ} (model : RationalCostModel) (W k limit : ℕ)
    (prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K)
    (state : State j (m*((prepare m k).K-1))) (hj : j<m*((prepare m k).K-1))
    (hc : StageAtBound model W k limit prep inputs state hj) :
    ∃ previousReserve,
      GeneralPaperSourceBasisPreparationStorage.StageAtBound model W k previousReserve prep inputs state hj ∧
      ∃ answer,(endpoint model W k prep inputs state hj).1=some answer ∧
        ∀ copied outerCopied innerCopied B,B≤previousReserve →
          B+window model W k copied outerCopied innerCopied prep inputs state hj answer≤limit := by
  obtain ⟨D,F,hPrevious,⟨answer,hr,hCache⟩,hSum⟩ := hc
  exact ⟨D,hPrevious,answer,hr,fun c o i B hB => (Nat.add_le_add hB (hCache c o i)).trans hSum⟩

theorem retained_preparation {T m j : ℕ} (model : RationalCostModel) (W k limit : ℕ)
    (prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K)
    (state : State j (m*((prepare m k).K-1))) (hj : j<m*((prepare m k).K-1))
    (hc : StageAtBound model W k limit prep inputs state hj) :
    ∃ answer,(endpoint model W k prep inputs state hj).1=some answer ∧
      ∀ oldCopied prepCopied copied outerCopied innerCopied,
        GeneralPaperSourceBasisRHSProductStorage.window model W k oldCopied prep inputs state hj+
        GeneralPaperSourceBasisPreparationStorage.window model W k prepCopied prep inputs state hj+
        window model W k copied outerCopied innerCopied prep inputs state hj answer≤limit := by
  obtain ⟨D,F,hPrevious,⟨answer,hr,hCache⟩,hSum⟩ := hc
  exact ⟨answer,hr,fun old pre c o i => (Nat.add_le_add
    (GeneralPaperSourceBasisPreparationStorage.retained_products model W k D prep inputs state hj hPrevious old pre)
    (hCache c o i)).trans hSum⟩

theorem cache_width (m k j : ℕ) (hj : j≤m*((prepare m k).K-1)) :
    GeneralPaperBasisCacheBitFacts.width j (prepare m k).H (m+1)≤GeneralPaperSourceBasisCacheStorageRates.operandWidth m k := by
  have h := GeneralPaperBasisCacheStageBits.paper_width m k j (prepare m k).S
    (GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows hj
  unfold GeneralPaperSourceBasisCacheStorageRates.operandWidth GeneralPaperSourceRayStorageWidth.width GeneralPaperSourceRayStorageWidth.rootWidth
  ring_nf at h ⊢
  omega

theorem budget_width (m k N : ℕ) (hN : binaryWordWidth N≤GeneralPaperSourceRayStorageWidth.gridWord m k) :
    GeneralPaperBasisBudgetBits.width N (GeneralPaperSourceBasisGridSize.auxiliaryBound m k)≤GeneralPaperSourceBasisCacheStorageRates.operandWidth m k := by
  have hn := binaryWordWidth_mono (Nat.le_succ N)
  have hb := binaryWordWidth_mono (Nat.le_succ (GeneralPaperSourceBasisGridSize.auxiliaryBound m k))
  simp only [Nat.succ_eq_add_one] at hn hb
  have h : GeneralPaperBasisBudgetBits.width N (GeneralPaperSourceBasisGridSize.auxiliaryBound m k)≤
      GeneralPaperBasisPreparationWidths.envelope (m*((prepare m k).K-1)) (m+1) N (prepare m k).H (GeneralPaperSourceBasisGridSize.auxiliaryBound m k) := by
    unfold GeneralPaperBasisBudgetBits.width GeneralPaperBasisPreparationWidths.envelope
    omega
  exact h.trans (GeneralPaperSourceBasisRHSProductStorage.operand_envelope m k N hN)

theorem from_ray {T m j : ℕ} (model : RationalCostModel) (W k copied outerCopied innerCopied : ℕ) (hm : 0<m)
    (dict : GeneralPaperDictionary.Dictionary T m (prepare m k).K) (v : RationalFieldSelector m)
    (S h N : ℕ) (hN : 0<N) (betaN : ℤ) (initialGrid : Vector (m*((prepare m k).K-1)))
    (state : State j (m*((prepare m k).K-1))) (hj : j<m*((prepare m k).K-1))
    (inv : Invariant dict v S h N betaN initialGrid (Nat.le_of_lt hj) state)
    (answer : GeneralPaperRayEndpoint.Answer T m (prepare m k).K)
    (hContract : GeneralPaperRayEndpointSound.Contract (S:=S) dict v h ((betaN:ℚ)/(N:ℚ))
      (reader (GeneralPaperBasisFreshPoint.run N betaN state.determinant state.adjugate state.rows initialGrid).point)
      (reader (GeneralPaperBasisDirection.run state.determinant state.adjugate state.rows (next hj)).velocity) answer)
    (hW : 1≤W) (hJ : binaryWordWidth (j+2)≤W) :
    cacheWindow model W copied outerCopied innerCopied dict.label state hj answer≤
      GeneralPaperBasisCacheStorage.profile model W j (GeneralPaperSourceBasisCacheStorageRates.operandWidth m k) := by
  have hc := GeneralPaperBasisCacheSize.cache_H k hm dict v S h N betaN initialGrid (Nat.le_of_lt hj) state inv
  have hb := GeneralPaperBasisAdvanceSize.from_ray k hm dict v S h N betaN initialGrid state hj inv answer hContract
  have hInv := GeneralPaperBasisStepSound.advance_valid dict v S h N hN betaN initialGrid state hj inv answer hContract
  unfold cacheWindow
  simp only [GeneralPaperBlockerRowPrice.data,GeneralPaperBasisDenseBits.data,
    GeneralPaperBasisAssemblyBits.column_data,GeneralPaperBasisArrayPrice.prefix_data]
  exact GeneralPaperBasisCacheStorage.bounded model W copied outerCopied innerCopied (prepare m k).H (m+1) _ hW hJ
    state.determinant state.adjugate (GeneralPaperBasisFreshRHS.minor state.rows (Nat.le_of_lt hj)) _ _ _
    inv.cache inv.nonzero hInv.nonzero hc.1 hc.2 hb.1 hb.2.1 hb.2.2.1 (cache_width m k j (Nat.le_of_lt hj))

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
      StageAtBound model W k (GeneralPaperSourceBasisCacheStorageRates.reservation model W m k) prep inputs state hj := by
  dsimp only
  intro j hj state inv
  let prep := GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b reciprocal
  let v := GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs
  let f := (GeneralPaperProxyClassifier.classify m k b).choice.proxy
  let inputs := GeneralPaperSharedBasisInputs.prepare k prep v f.num f.den reciprocal
  let dim := m*((prepare m k).K-1)
  let R := GeneralPaperSourceBasisCacheStorageRates.operandWidth m k
  have hOld := GeneralPaperSourceBasisPreparationStorage.source_stage model W k Qv hm hQv weights hp hs b hb reciprocal
    hW hK hM hIndex hDim hBatch hFinalIndex j hj state inv
  have hN : 0 < inputs.controls.N := (GeneralPaperInitializerSelectedControls.positive m k hm b hb reciprocal).1
  have hAux := GeneralPaperSourceBasisGridSize.auxiliary (m:=m) k b hb reciprocal
  have hGridWord := GeneralPaperSourceRayStorageWidth.grid_bound m k b hb reciprocal
  change binaryWordWidth inputs.controls.N≤GeneralPaperSourceRayStorageWidth.gridWord m k at hGridWord
  have hBudget := GeneralPaperBasisBudgetStorage.bounded model W inputs.controls.N _ R inputs.betaN hAux (budget_width m k inputs.controls.N hGridWord)
  have hJ : binaryWordWidth (j+2)≤W := (binaryWordWidth_mono (show j+2≤dim+1 by omega)).trans hDim
  obtain ⟨a,ha⟩ := next_velocity state.determinant state.adjugate state.rows (next hj) rfl
  have hStart : GeneralPaperAffineConstraintRows.Feasible prep.dictionary.label (GeneralPaperStrictScore.score v (prepare m k).S) prep.threshold
      (((inputs.betaN:ℚ)/(inputs.controls.N:ℚ):ℚ):ℝ)
      (fun b => (reader (GeneralPaperBasisFreshPoint.run inputs.controls.N inputs.betaN state.determinant state.adjugate state.rows inputs.initialGrid).point b:ℝ)) := by
    simpa only [Rat.cast_div,Rat.cast_intCast,Rat.cast_natCast,reader,GeneralPaperBasisFreshPointSound.values] using inv.feasible
  obtain ⟨answer,hNative,hContract⟩ := GeneralPaperRayEndpointSound.endpoint_sound (GeneralPaperScoreScaleParameters.prepare m k).depth
    prep.dictionary v (GeneralPaperScoreScaleParameters.labels_positive m k) (GeneralPaperScoreScaleParameters.score_cap m k)
    prep.threshold ((inputs.betaN:ℚ)/(inputs.controls.N:ℚ)) _ _ hStart a ha
  have hRay : (endpoint model W k prep inputs state hj).1=some answer := by
    unfold endpoint
    dsimp only
    rw [GeneralPaperBasisPreparationBits.point_data,GeneralPaperBasisPreparationBits.direction_data,GeneralPaperBasisBudgetBits.data,
      GeneralPaperEndpointBits.data,GeneralPaperSharedBasisInputs.matrix_eq]
    exact hNative
  refine ⟨GeneralPaperSourceBasisPreparationStorageRates.reservation model W m k,
    GeneralPaperSourceBasisCacheStorageRates.sourceProfile model W m k,hOld,⟨answer,hRay,?_⟩,le_rfl⟩
  intro copied outerCopied innerCopied
  have hCache := from_ray model W k copied outerCopied innerCopied hm prep.dictionary v (prepare m k).S prep.threshold
    inputs.controls.N hN inputs.betaN inputs.initialGrid state hj inv answer hContract hW hJ
  have hNew : window model W k copied outerCopied innerCopied prep inputs state hj answer≤
      GeneralPaperSourceBasisCacheStorageRates.profile model W j R := Nat.add_le_add hBudget hCache
  exact hNew.trans (GeneralPaperSourceBasisCacheStorageRates.dimensions_mono model W j dim R (Nat.le_of_lt hj))

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
      StageAtBound model W k (GeneralPaperSourceBasisCacheStorageRates.reservation model W m k) prep inputs state hj := by
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

end Blotto.GeneralPaperSourceBasisCacheStorage
