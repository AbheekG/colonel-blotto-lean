import Blotto.GeneralPaperSourceRefinementStorageContext

/-! Complete refinement-storage coverage at the actual source endpoint.
The actual priced static choice determines the high-search bracket. Every
executed pair/final-budget refinement and all its preparation/search/return
phases inherit native source-derived query bounds. Reached bit-controller
states and their return equations are joined without a height/cost oracle. -/
namespace Blotto.GeneralPaperSourceEndpointRefinementStorage
open RationalOrderCell GeneralPaperProxyParameters GeneralPaperBasisStoredProducts
open GeneralPaperBasisState GeneralPaperBasisInvariant GeneralPaperBasisOriginalDirection
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192

def StageAtBound {T m j : ℕ} (model : RationalCostModel) (W k limit : ℕ)
    (prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K)
    (state : State j (m*((prepare m k).K-1))) (hj : j<m*((prepare m k).K-1)) : Prop :=
  let x := reader (GeneralPaperBasisFreshPoint.run inputs.controls.N inputs.betaN state.determinant state.adjugate state.rows inputs.initialGrid).point
  let w := reader (GeneralPaperBasisDirection.run state.determinant state.adjugate state.rows (next hj)).velocity
  ∃ c,(GeneralPaperStaticScanPrice.run model.rat W prep.dictionary.label x w).choice=some c ∧
    GeneralPaperRayParametricRefinementCoverage.high model W inputs.matrix x w (prepare m k).S prep.threshold
      ((inputs.betaN:ℚ)/(inputs.controls.N:ℚ)) 0 c.time
      (GeneralPaperSourceRefinementStorageContext.AtBound model W k prep inputs state hj limit)

def StageBound {T m j : ℕ} (model : RationalCostModel) (W k : ℕ)
    (prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K)
    (state : State j (m*((prepare m k).K-1))) (hj : j<m*((prepare m k).K-1)) : Prop :=
  StageAtBound model W k (GeneralPaperSourceCrossingRefinementRates.reservation model W m k) prep inputs state hj

theorem stage_mono {T m j : ℕ} (model : RationalCostModel) (W k : ℕ)
    (prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K)
    (state : State j (m*((prepare m k).K-1))) (hj : j<m*((prepare m k).K-1)) (B C : ℕ) (hBC : B≤C)
    (h : StageAtBound model W k B prep inputs state hj) : StageAtBound model W k C prep inputs state hj := by
  let x := reader (GeneralPaperBasisFreshPoint.run inputs.controls.N inputs.betaN state.determinant state.adjugate state.rows inputs.initialGrid).point
  let w := reader (GeneralPaperBasisDirection.run state.determinant state.adjugate state.rows (next hj)).velocity
  obtain ⟨c,hScan,hCoverage⟩ := h
  refine ⟨c,hScan,?_⟩
  exact GeneralPaperRayParametricRefinementCoverage.high_mono model W inputs.matrix x w (prepare m k).S prep.threshold
    ((inputs.betaN:ℚ)/(inputs.controls.N:ℚ)) _ _
    (fun lo hi points hh => GeneralPaperSourceRefinementStorageContext.at_bound_mono model W k prep inputs state hj B C hBC lo hi points hh)
    0 c.time hCoverage

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
      StageBound model W k prep inputs state hj := by
  dsimp only
  intro j hj state inv
  let prep := GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b reciprocal
  let v := GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs
  let f := (GeneralPaperProxyClassifier.classify m k b).choice.proxy
  let inputs := GeneralPaperSharedBasisInputs.prepare k prep v f.num f.den reciprocal
  let x := reader (GeneralPaperBasisFreshPoint.run inputs.controls.N inputs.betaN state.determinant state.adjugate state.rows inputs.initialGrid).point
  let w := reader (GeneralPaperBasisDirection.run state.determinant state.adjugate state.rows (next hj)).velocity
  have hReady := GeneralPaperSourceRefinementStorageContext.source_stage model W k Qv hm hQv weights hp hs b hb reciprocal
    hW hK hM hIndex hDim hBatch j hj state inv
  obtain ⟨c,hScan,hLo,hHi,_⟩ := GeneralPaperSourceRayQueryStorage.source_stage model W k Qv hm hQv weights hp hs b hb reciprocal
    hW hK hM hIndex j hj state inv
  have hN : 0 < inputs.controls.N := (GeneralPaperInitializerSelectedControls.positive m k hm b hb reciprocal).1
  have hD := Int.natAbs_pos.mpr inv.nonzero
  have hx := GeneralPaperRayAnchorBound.point k prep.dictionary v (prepare m k).S prep.threshold inputs.controls.N hN
    inputs.betaN inputs.initialGrid (Nat.le_of_lt hj) state inv
  have hw := GeneralPaperRayAnchorBound.direction k hm prep.dictionary v (prepare m k).S prep.threshold inputs.controls.N
    inputs.betaN inputs.initialGrid (Nat.le_of_lt hj) state inv (next hj) rfl
  have hBeta := GeneralPaperRayAnchorBound.budget inputs.controls.N hN state.determinant.natAbs inputs.betaN
  have hHeight := GeneralPaperRayUniformSize.static_time hm (Nat.mul_pos hN hD) hD prep.dictionary.label
    (GeneralPaperRayQueryWork.scores inputs.matrix) prep.threshold _ x w hx hw hBeta c hScan
  have hScan' : (GeneralPaperStaticScanPrice.run model.rat W prep.dictionary.label x w).choice=some c :=
    (GeneralPaperStaticScanPrice.data model.rat W prep.dictionary.label x w).trans hScan
  refine ⟨c,hScan',?_⟩
  exact GeneralPaperRayParametricRefinementCoverage.high_bounded model W (inputs.controls.N*state.determinant.natAbs)
    state.determinant.natAbs 1 (j*(prepare m k).H*(m+1)+1) inputs.betaN.natAbs (Nat.mul_pos hN hD) hD
    (GeneralPaperScoreScaleParameters.labels_positive m k) inputs.matrix x w hx hw (prepare m k).S prep.threshold _ hBeta
    (GeneralPaperSourceRefinementStorageContext.BatchBound model W k prep inputs state hj) hReady 0 c.time
    (by norm_num) hLo hHi (GeneralPaperEndpointPriceFacts.zero_height _ _ _ _ _ _) hHeight

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
      inputs.controls.N inputs.betaN inputs.initialGrid j (Nat.le_of_lt hj)).1=some state ∧ StageBound model W k prep inputs state hj := by
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
      inputs.controls.N inputs.betaN inputs.initialGrid j (Nat.le_of_lt hj)=some state := by
    rw [GeneralPaperSharedBasisInputs.matrix_eq]
    exact hr
  refine ⟨state,?_,source_stage model W k Qv hm hQv weights hp hs b hb reciprocal hW hK hM hIndex hDim hBatch j hj state inv⟩
  exact (GeneralPaperBasisControllerBits.stages_data model W _ _ _ _ _ _ _ _ _).trans hReturn

end Blotto.GeneralPaperSourceEndpointRefinementStorage
