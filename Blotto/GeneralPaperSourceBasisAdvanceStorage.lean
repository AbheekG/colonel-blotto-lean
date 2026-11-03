import Blotto.GeneralPaperSourceBasisAdvanceStorageRates

/-! Complete actual reached-source native basis advance storage. Prefix,
row-reference append and the parent return coexist with earlier cache/
point/direction/ray windows. Endpoint and original invariant facts derive
all new-state, row/vector payload and native partial-field bounds. -/
namespace Blotto.GeneralPaperSourceBasisAdvanceStorage
open RationalOrderCell GeneralPaperProxyParameters GeneralPaperBasisStoredProducts
open GeneralPaperBasisState GeneralPaperBasisInvariant GeneralPaperBasisOriginalDirection
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 8192

def endpoint {T m j : ℕ} (model : RationalCostModel) (W k : ℕ)
    (prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K)
    (state : State j (m*((prepare m k).K-1))) (hj : j<m*((prepare m k).K-1)) :=
  GeneralPaperSourceBasisCacheStorage.endpoint model W k prep inputs state hj

def window {T m j : ℕ} (model : RationalCostModel) (W k prefixCopied appendCopied : ℕ)
    (prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (_inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K)
    (state : State j (m*((prepare m k).K-1))) (hj : j<m*((prepare m k).K-1))
    (answer : GeneralPaperRayEndpoint.Answer T m (prepare m k).K) : ℕ :=
  GeneralPaperBasisAdvanceReturnStorage.window model W prefixCopied appendCopied prep.dictionary.label state hj answer

def StageAtBound {T m j : ℕ} (model : RationalCostModel) (W k limit : ℕ)
    (prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K)
    (state : State j (m*((prepare m k).K-1))) (hj : j<m*((prepare m k).K-1)) : Prop :=
  ∃ previousReserve cacheReserve,
    GeneralPaperSourceBasisCacheStorage.StageAtBound model W k previousReserve prep inputs state hj ∧
      (∃ answer,(endpoint model W k prep inputs state hj).1=some answer ∧
        ∀ prefixCopied appendCopied,window model W k prefixCopied appendCopied prep inputs state hj answer≤cacheReserve) ∧
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
      GeneralPaperSourceBasisCacheStorage.StageAtBound model W k previousReserve prep inputs state hj ∧
      ∃ answer,(endpoint model W k prep inputs state hj).1=some answer ∧
        ∀ prefixCopied appendCopied B,B≤previousReserve →
          B+window model W k prefixCopied appendCopied prep inputs state hj answer≤limit := by
  obtain ⟨D,F,hPrevious,⟨answer,hr,hCache⟩,hSum⟩ := hc
  exact ⟨D,hPrevious,answer,hr,fun c a B hB => (Nat.add_le_add hB (hCache c a)).trans hSum⟩

theorem retained_cache {T m j : ℕ} (model : RationalCostModel) (W k limit : ℕ)
    (prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K)
    (state : State j (m*((prepare m k).K-1))) (hj : j<m*((prepare m k).K-1))
    (hc : StageAtBound model W k limit prep inputs state hj) :
    ∃ answer,(endpoint model W k prep inputs state hj).1=some answer ∧
      ∀ copied outerCopied innerCopied prefixCopied appendCopied,
        GeneralPaperSourceBasisCacheStorage.window model W k copied outerCopied innerCopied prep inputs state hj answer+
          window model W k prefixCopied appendCopied prep inputs state hj answer≤limit := by
  obtain ⟨D,F,hPrevious,⟨answer,hr,hAdvance⟩,hSum⟩ := hc
  obtain ⟨D0,F0,_,⟨oldAnswer,oldReturn,hCache⟩,hOldSum⟩ := hPrevious
  have he : oldAnswer=answer := Option.some.inj (oldReturn.symm.trans hr)
  subst oldAnswer
  refine ⟨answer,hr,?_⟩
  intro c o i p a
  exact (Nat.add_le_add ((hCache c o i).trans (show F0≤D by omega)) (hAdvance p a)).trans hSum

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
      StageAtBound model W k (GeneralPaperSourceBasisAdvanceStorageRates.reservation model W m k) prep inputs state hj := by
  dsimp only
  intro j hj state inv
  let prep := GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b reciprocal
  let v := GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs
  let f := (GeneralPaperProxyClassifier.classify m k b).choice.proxy
  let inputs := GeneralPaperSharedBasisInputs.prepare k prep v f.num f.den reciprocal
  have hOld := GeneralPaperSourceBasisCacheStorage.source_stage model W k Qv hm hQv weights hp hs b hb reciprocal
    hW hK hM hIndex hDim hBatch hFinalIndex j hj state inv
  have hN : 0 < inputs.controls.N := (GeneralPaperInitializerSelectedControls.positive m k hm b hb reciprocal).1
  obtain ⟨a,ha⟩ := next_velocity state.determinant state.adjugate state.rows (next hj) rfl
  have hStart : GeneralPaperAffineConstraintRows.Feasible prep.dictionary.label (GeneralPaperStrictScore.score v (prepare m k).S) prep.threshold
      (((inputs.betaN:ℚ)/(inputs.controls.N:ℚ):ℚ):ℝ)
      (fun b => (reader (GeneralPaperBasisFreshPoint.run inputs.controls.N inputs.betaN state.determinant state.adjugate state.rows inputs.initialGrid).point b:ℝ)) := by
    simpa only [Rat.cast_div,Rat.cast_intCast,Rat.cast_natCast,reader,GeneralPaperBasisFreshPointSound.values] using inv.feasible
  obtain ⟨answer,hNative,hContract⟩ := GeneralPaperRayEndpointSound.endpoint_sound (GeneralPaperScoreScaleParameters.prepare m k).depth
    prep.dictionary v (GeneralPaperScoreScaleParameters.labels_positive m k) (GeneralPaperScoreScaleParameters.score_cap m k)
    prep.threshold ((inputs.betaN:ℚ)/(inputs.controls.N:ℚ)) _ _ hStart a ha
  have hRay : (endpoint model W k prep inputs state hj).1=some answer := by
    unfold endpoint GeneralPaperSourceBasisCacheStorage.endpoint
    dsimp only
    rw [GeneralPaperBasisPreparationBits.point_data,GeneralPaperBasisPreparationBits.direction_data,GeneralPaperBasisBudgetBits.data,
      GeneralPaperEndpointBits.data,GeneralPaperSharedBasisInputs.matrix_eq]
    exact hNative
  refine ⟨GeneralPaperSourceBasisCacheStorageRates.reservation model W m k,
    GeneralPaperSourceBasisAdvanceStorageRates.sourceProfile model W m k,hOld,⟨answer,hRay,?_⟩,le_rfl⟩
  intro prefixCopied appendCopied
  exact GeneralPaperBasisAdvanceReturnStorage.from_ray model W k prefixCopied appendCopied hm prep.dictionary v (prepare m k).S prep.threshold
    inputs.controls.N hN inputs.betaN inputs.initialGrid state hj inv answer hContract hW hDim

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
      StageAtBound model W k (GeneralPaperSourceBasisAdvanceStorageRates.reservation model W m k) prep inputs state hj := by
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

end Blotto.GeneralPaperSourceBasisAdvanceStorage
