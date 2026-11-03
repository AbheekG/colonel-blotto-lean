import Blotto.GeneralPaperSourceRayStorageWidth

/-! Every actual reached source basis stage has a static endpoint probe
whose complete local query-phase storage fits one source-wide profile.
Feasibility, nonzero determinant, next velocity, grid, auxiliary numerator,
probe interval/height and copied scores are all derived internally. Later
high-search probes and outer query owners remain separate joins. -/
namespace Blotto.GeneralPaperSourceRayQueryStorage
open RationalOrderCell GeneralPaperProxyParameters GeneralPaperBasisStoredProducts
open GeneralPaperBasisState GeneralPaperBasisInvariant GeneralPaperBasisOriginalDirection
open GeneralPaperRayRationalBound
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 4500000
set_option maxRecDepth 8192

def profile (model : RationalCostModel) (W m k : ℕ) : ℕ :=
  GeneralPaperRayQueryStorageEnvelope.profile model W m (prepare m k).K (prepare m k).S
    (GeneralPaperSourceRayStorageWidth.width m k)

def StageBound {T m j : ℕ} (model : RationalCostModel) (W k : ℕ)
    (prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K)
    (state : State j (m*((prepare m k).K-1))) (hj : j<m*((prepare m k).K-1)) : Prop :=
  let x := reader (GeneralPaperBasisFreshPoint.run inputs.controls.N inputs.betaN state.determinant state.adjugate state.rows inputs.initialGrid).point
  let w := reader (GeneralPaperBasisDirection.run state.determinant state.adjugate state.rows (next hj)).velocity
  ∃ c : GeneralPaperRayMinimum.Choice (GeneralPaperStaticRayRows.StaticIndex T m (prepare m k).K),
    (GeneralPaperStaticRayScan.scan prep.dictionary.label x w).choice=some c ∧ 0≤c.time ∧ c.time≤1 ∧
      ∀ phase : GeneralPaperRayQueryStorage.Phase model W inputs.matrix x w c.time (prepare m k).S,
        GeneralPaperRayQueryStorage.window model W inputs.matrix x w c.time (prepare m k).S prep.threshold phase≤profile model W m k

theorem source_stage {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv)
    (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool)
    (hW : 1≤W) (hK : binaryWordWidth ((prepare m k).K+1)≤W) (hM : binaryWordWidth (m+1)≤W)
    (hIndex : binaryWordWidth ((prepare m k).S+2)≤W) :
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
  have hN : 0 < inputs.controls.N := (GeneralPaperInitializerSelectedControls.positive m k hm b hb reciprocal).1
  have hD := Int.natAbs_pos.mpr inv.nonzero
  have hx := GeneralPaperRayAnchorBound.point k prep.dictionary v (prepare m k).S prep.threshold inputs.controls.N hN
    inputs.betaN inputs.initialGrid (Nat.le_of_lt hj) state inv
  have hw := GeneralPaperRayAnchorBound.direction k hm prep.dictionary v (prepare m k).S prep.threshold inputs.controls.N
    inputs.betaN inputs.initialGrid (Nat.le_of_lt hj) state inv (next hj) rfl
  have hBeta := GeneralPaperRayAnchorBound.budget inputs.controls.N hN state.determinant.natAbs inputs.betaN
  have hStart : GeneralPaperAffineConstraintRows.Feasible prep.dictionary.label (GeneralPaperStrictScore.score v (prepare m k).S)
      prep.threshold (((inputs.betaN:ℚ)/(inputs.controls.N:ℚ):ℚ):ℝ) (fun a => (x a:ℝ)) := by
    simpa only [Rat.cast_div,Rat.cast_intCast,Rat.cast_natCast,x,reader,GeneralPaperBasisFreshPointSound.values] using inv.feasible
  obtain ⟨a,hVelocity⟩ := next_velocity state.determinant state.adjugate state.rows (next hj) rfl
  obtain ⟨c,hScan,hNonnegative,hOne,_,_⟩ := GeneralPaperStaticRaySound.finite_endpoint prep.dictionary.label
    (GeneralPaperStrictScore.score v (prepare m k).S) prep.threshold _ x w hStart a hVelocity
  have hHeight := GeneralPaperRayUniformSize.static_time hm (Nat.mul_pos hN hD) hD prep.dictionary.label
    (GeneralPaperRayQueryWork.scores inputs.matrix) prep.threshold _ x w hx hw hBeta c hScan
  have hCache := (GeneralPaperBasisCacheSize.cache_H k hm prep.dictionary v (prepare m k).S prep.threshold
    inputs.controls.N inputs.betaN inputs.initialGrid (Nat.le_of_lt hj) state inv).1
  have hAux : inputs.betaN.natAbs≤GeneralPaperSourceBasisGridSize.auxiliaryBound m k :=
    GeneralPaperSourceBasisGridSize.auxiliary (m:=m) k b hb reciprocal
  have hRoot := GeneralPaperSourceRayStorageWidth.root_bound m k j b hb reciprocal state.determinant.natAbs
    inputs.betaN.natAbs (Nat.le_of_lt hj) hCache hAux
  have hT : RationalHeight c.time (2*GeneralPaperSourceRayStorageWidth.rootWidth m k+3) :=
    (hHeight.mono hRoot).mono (by omega)
  have hWord := GeneralPaperSourceRayStorageWidth.probe_word m k j b hb reciprocal state.determinant.natAbs
    inputs.betaN.natAbs (Nat.le_of_lt hj) hCache hAux c.time hT
  have hThreshold : prep.threshold≤(prepare m k).S := GeneralPaperTransferPreparation.threshold_le _ _ _ _ _ _ _ _
  have hScores : ∀ a l,((inputs.matrix.read a).read l).1≤(prepare m k).S := by
    intro a l
    rw [GeneralPaperSharedBasisInputs.matrix_eq]
    erw [GeneralPaperScoreMatrixWork.matrix_data (GeneralPaperScoreScaleParameters.prepare m k).depth prep.dictionary v
      (prepare m k).S (GeneralPaperScoreScaleParameters.labels_positive m k) (GeneralPaperScoreScaleParameters.score_cap m k)]
    simp only [FixedArrayTable.read_ofFn]
    convert GeneralPaperEncodedScoreMatrixStorage.score_bound v (prepare m k).S
      (GeneralPaperScoreScaleParameters.labels_positive m k) a l using 1
    rfl
  refine ⟨c,hScan,hNonnegative,hOne,?_⟩
  intro phase
  have hLocal := GeneralPaperRayQueryStorage.all_phases model W (prepare m k).S prep.threshold
    (inputs.controls.N*state.determinant.natAbs) state.determinant.natAbs 1 (j*(prepare m k).H*(m+1)+1)
    (Nat.mul_pos hN hD) (show state.determinant.natAbs∣inputs.controls.N*state.determinant.natAbs from ⟨inputs.controls.N,by ring⟩)
    inputs.matrix hScores x w hx hw c.time ⟨hNonnegative,hOne⟩ hThreshold hW hK hM hIndex phase
  exact hLocal.trans (GeneralPaperRayQueryStorageEnvelope.dominates model W m (prepare m k).K (prepare m k).S
    _ _ (GeneralPaperSourceRayStorageWidth.width m k) hWord)

theorem actual_reached {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv)
    (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool)
    (hW : 1≤W) (hK : binaryWordWidth ((prepare m k).K+1)≤W) (hM : binaryWordWidth (m+1)≤W)
    (hIndex : binaryWordWidth ((prepare m k).S+2)≤W) (j : ℕ) (hj : j<m*((prepare m k).K-1)) :
    let prep := GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b reciprocal
    let v := GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs
    let f := (GeneralPaperProxyClassifier.classify m k b).choice.proxy
    let inputs := GeneralPaperSharedBasisInputs.prepare k prep v f.num f.den reciprocal
    ∃ state,GeneralPaperBasisController.stages prep.dictionary.label inputs.matrix (prepare m k).S prep.threshold
      inputs.controls.N inputs.betaN inputs.initialGrid j (Nat.le_of_lt hj)=some state ∧ StageBound model W k prep inputs state hj := by
  let prep := GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b reciprocal
  let v := GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs
  let f := (GeneralPaperProxyClassifier.classify m k b).choice.proxy
  let inputs := GeneralPaperSharedBasisInputs.prepare k prep v f.num f.den reciprocal
  have hStart := GeneralPaperSourceBasisInputValidity.actual_start k Qv hm hQv weights hp hs b hb reciprocal
  have hN : 0 < inputs.controls.N := (GeneralPaperInitializerSelectedControls.positive m k hm b hb reciprocal).1
  obtain ⟨state,hr,inv⟩ := GeneralPaperBasisControllerSound.stages_valid (GeneralPaperScoreScaleParameters.prepare m k).depth
    prep.dictionary v (GeneralPaperScoreScaleParameters.labels_positive m k) (prepare m k).S prep.threshold inputs.controls.N hN
    (GeneralPaperScoreScaleParameters.score_cap m k) inputs.betaN inputs.initialGrid hStart j (Nat.le_of_lt hj)
  refine ⟨state,?_,source_stage model W k Qv hm hQv weights hp hs b hb reciprocal hW hK hM hIndex j hj state inv⟩
  rw [GeneralPaperSharedBasisInputs.matrix_eq]
  exact hr

end Blotto.GeneralPaperSourceRayQueryStorage
