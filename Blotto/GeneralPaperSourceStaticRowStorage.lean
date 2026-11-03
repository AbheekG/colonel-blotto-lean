import Blotto.GeneralPaperSourceStaticRowRates

/-! Actual reached-source sparse static-row residual storage. Every literal
box/order/retained-budget row is covered. The original matrix and packed
ray owners are retained; previous generation/recursion contracts persist.
Outer static enumeration/row-constructor/minimum lifetimes remain separate. -/
namespace Blotto.GeneralPaperSourceStaticRowStorage
open RationalOrderCell GeneralPaperProxyParameters GeneralPaperBasisStoredProducts
open GeneralPaperBasisState GeneralPaperBasisInvariant GeneralPaperBasisOriginalDirection
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 7000000
set_option maxRecDepth 8192

def StageAtBound {T m j : ℕ} (model : RationalCostModel) (W k limit : ℕ)
    (prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K)
    (state : State j (m*((prepare m k).K-1))) (hj : j<m*((prepare m k).K-1)) : Prop :=
  let x := reader (GeneralPaperBasisFreshPoint.run inputs.controls.N inputs.betaN state.determinant state.adjugate state.rows inputs.initialGrid).point
  let w := reader (GeneralPaperBasisDirection.run state.determinant state.adjugate state.rows (next hj)).velocity
  ∃ previousReserve rowReserve,
    GeneralPaperSourceEndpointCallerStorage.StageAtBound model W k previousReserve prep inputs state hj ∧
      (∀ i : GeneralPaperStaticRayRows.StaticIndex T m (prepare m k).K,
        GeneralPaperSourceRayQueryOwners.window model W k inputs state hj+
          GeneralPaperStaticRowResidualStorage.window model W prep.dictionary.label x w i≤previousReserve+rowReserve) ∧
        previousReserve+rowReserve≤limit

theorem stage_mono {T m j : ℕ} (model : RationalCostModel) (W k : ℕ)
    (prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K)
    (state : State j (m*((prepare m k).K-1))) (hj : j<m*((prepare m k).K-1)) (B C : ℕ) (hBC : B≤C)
    (h : StageAtBound model W k B prep inputs state hj) : StageAtBound model W k C prep inputs state hj := by
  obtain ⟨D,F,hPrevious,hRows,hSum⟩ := h
  exact ⟨D,F,hPrevious,hRows,hSum.trans hBC⟩

theorem source_stage {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv)
    (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool)
    (hW : 1≤W) (hK : binaryWordWidth ((prepare m k).K+1)≤W) (hM : binaryWordWidth (m+1)≤W)
    (hIndex : binaryWordWidth ((prepare m k).S+2)≤W) (hDim : binaryWordWidth (m*((prepare m k).K-1)+1)≤W)
    (hBatch : binaryWordWidth (((prepare m k).S+1)*((prepare m k).K*(prepare m k).K)+3)≤W) :
    let prep := GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b reciprocal
    let v := GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs
    let f := (GeneralPaperProxyClassifier.classify m k b).choice.proxy
    let inputs := GeneralPaperSharedBasisInputs.prepare k prep v f.num f.den reciprocal
    ∀ j (hj : j<m*((prepare m k).K-1)) (state : State j (m*((prepare m k).K-1))),
      Invariant prep.dictionary v (prepare m k).S prep.threshold inputs.controls.N inputs.betaN inputs.initialGrid (Nat.le_of_lt hj) state →
      StageAtBound model W k (GeneralPaperSourceStaticRowRates.reservation model W m k) prep inputs state hj := by
  dsimp only
  intro j hj state inv
  let prep := GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b reciprocal
  let v := GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs
  let f := (GeneralPaperProxyClassifier.classify m k b).choice.proxy
  let inputs := GeneralPaperSharedBasisInputs.prepare k prep v f.num f.den reciprocal
  let x := reader (GeneralPaperBasisFreshPoint.run inputs.controls.N inputs.betaN state.determinant state.adjugate state.rows inputs.initialGrid).point
  let w := reader (GeneralPaperBasisDirection.run state.determinant state.adjugate state.rows (next hj)).velocity
  let R := GeneralPaperRayUniformSize.width (inputs.controls.N*state.determinant.natAbs) state.determinant.natAbs
    m 1 (j*(prepare m k).H*(m+1)+1) inputs.betaN.natAbs
  let H := GeneralPaperSourceRayStorageWidth.width m k
  have hN : 0 < inputs.controls.N := (GeneralPaperInitializerSelectedControls.positive m k hm b hb reciprocal).1
  have hD := Int.natAbs_pos.mpr inv.nonzero
  have hx := GeneralPaperRayAnchorBound.point k prep.dictionary v (prepare m k).S prep.threshold inputs.controls.N hN
    inputs.betaN inputs.initialGrid (Nat.le_of_lt hj) state inv
  have hw := GeneralPaperRayAnchorBound.direction k hm prep.dictionary v (prepare m k).S prep.threshold inputs.controls.N
    inputs.betaN inputs.initialGrid (Nat.le_of_lt hj) state inv (next hj) rfl
  have hCache := (GeneralPaperBasisCacheSize.cache_H k hm prep.dictionary v (prepare m k).S prep.threshold
    inputs.controls.N inputs.betaN inputs.initialGrid (Nat.le_of_lt hj) state inv).1
  have hAux : inputs.betaN.natAbs≤GeneralPaperSourceBasisGridSize.auxiliaryBound m k := GeneralPaperSourceBasisGridSize.auxiliary (m:=m) k b hb reciprocal
  have hRoot := GeneralPaperSourceRayStorageWidth.root_bound m k j b hb reciprocal state.determinant.natAbs inputs.betaN.natAbs (Nat.le_of_lt hj) hCache hAux
  change R≤GeneralPaperSourceRayStorageWidth.rootWidth m k at hRoot
  have hRH : R≤H := by dsimp only [H]; unfold GeneralPaperSourceRayStorageWidth.width; omega
  have hOld := GeneralPaperSourceEndpointCallerStorage.source_stage model W k Qv hm hQv weights hp hs b hb reciprocal
    hW hK hM hIndex hDim hBatch j hj state inv
  have hOwners := GeneralPaperSourceRayQueryOwners.source_stage model W k Qv hm hQv weights hp hs b hb reciprocal hW hDim j hj state inv
  have hOuter : GeneralPaperSourceRayQueryOwners.window model W k inputs state hj≤GeneralPaperSourceParametricCallerRates.reservation model W m k :=
    hOwners.trans (by
      unfold GeneralPaperSourceParametricCallerRates.reservation GeneralPaperSourceAffineLayerRates.reservation
        GeneralPaperSourceAffineInputRates.reservation GeneralPaperSourceCrossingStreamRates.reservation
        GeneralPaperSourceCrossingOperandStorageRates.reservation GeneralPaperSourceCrossingRefinementRates.reservation
        GeneralPaperSourceEndpointOwnerStorage.profile
      omega)
  refine ⟨GeneralPaperSourceParametricCallerRates.reservation model W m k,
    GeneralPaperSourceStaticRowRates.sourceProfile model W m k,hOld,?_,le_rfl⟩
  intro i
  have hRow := GeneralPaperStaticRowResidualStorage.bounded model W (inputs.controls.N*state.determinant.natAbs) state.determinant.natAbs
    1 (j*(prepare m k).H*(m+1)+1) inputs.betaN.natAbs hm (Nat.mul_pos hN hD) hD prep.dictionary.label x w hx hw i
  have hWhole : GeneralPaperStaticRowResidualStorage.window model W prep.dictionary.label x w i≤
      GeneralPaperSourceStaticRowRates.sourceProfile model W m k := hRow.trans
        (GeneralPaperSourceStaticRowRates.height_mono model W m (prepare m k).K (prepare m k).S R H hRH)
  exact Nat.add_le_add hOuter hWhole

theorem actual_reached {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv)
    (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool)
    (hW : 1≤W) (hK : binaryWordWidth ((prepare m k).K+1)≤W) (hM : binaryWordWidth (m+1)≤W)
    (hIndex : binaryWordWidth ((prepare m k).S+2)≤W) (hDim : binaryWordWidth (m*((prepare m k).K-1)+1)≤W)
    (hBatch : binaryWordWidth (((prepare m k).S+1)*((prepare m k).K*(prepare m k).K)+3)≤W)
    (j : ℕ) (hj : j<m*((prepare m k).K-1)) :
    let prep := GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b reciprocal
    let v := GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs
    let f := (GeneralPaperProxyClassifier.classify m k b).choice.proxy
    let inputs := GeneralPaperSharedBasisInputs.prepare k prep v f.num f.den reciprocal
    ∃ state,(GeneralPaperBasisControllerBits.stages model W prep.dictionary.label inputs.matrix (prepare m k).S prep.threshold
      inputs.controls.N inputs.betaN inputs.initialGrid j (Nat.le_of_lt hj)).1=some state ∧
      StageAtBound model W k (GeneralPaperSourceStaticRowRates.reservation model W m k) prep inputs state hj := by
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
  refine ⟨state,?_,source_stage model W k Qv hm hQv weights hp hs b hb reciprocal hW hK hM hIndex hDim hBatch j hj state inv⟩
  exact (GeneralPaperBasisControllerBits.stages_data model W _ _ _ _ _ _ _ _ _).trans hReturn

end Blotto.GeneralPaperSourceStaticRowStorage
