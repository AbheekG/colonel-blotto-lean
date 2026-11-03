import Blotto.GeneralPaperBasisPreparationWidths

/-! Native original-basis invariants and selected source/grid/classifier
data discharge complete fresh-preparation bit prices. Reached actual stages
are joined without supplied RHS, prefix-height or preparation-cost oracles.
Surrounding source/grid construction and all global capacities remain open.
-/
namespace Blotto.GeneralPaperBasisPreparationStageBits
open RationalOrderCell GeneralPaperBasisStoredProducts GeneralPaperBasisState GeneralPaperBasisInvariant
open GeneralPaperProxyParameters
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 9000000
set_option maxRecDepth 4096

theorem phase_scale (j d W P : ℕ) (hj : j≤d) :
    4096*(j+1)*(j+d+2)*(W+P)≤8192*(d+1)^2*(W+P) := by
  have hh := Nat.mul_le_mul (show j+1≤d+1 by omega) (show j+d+2≤2*(d+1) by omega)
  have hs : 4096*(j+1)*(j+d+2)≤8192*(d+1)^2 := by nlinarith only [hh]
  exact Nat.mul_le_mul_right (W+P) hs

theorem from_invariant {T m j : ℕ} (model : RationalCostModel) (W k : ℕ) (hm : 0<m)
    (dict : GeneralPaperDictionary.Dictionary T m (prepare m k).K) (v : RationalFieldSelector m)
    (S h N B : ℕ) (betaN : ℤ) (initialGrid : Vector (m*((prepare m k).K-1)))
    (state : State j (m*((prepare m k).K-1))) (hj : j≤m*((prepare m k).K-1))
    (inv : Invariant dict v S h N betaN initialGrid hj state)
    (hBeta : betaN.natAbs≤B) (hGrid : ∀ i,(initialGrid.read i).natAbs≤N)
    (next : Fin (m*((prepare m k).K-1))) (hW : 1≤W) (hDim : binaryWordWidth (m*((prepare m k).K-1)+1)≤W) :
    (GeneralPaperBasisPreparationBits.point model.rat W N betaN state.determinant state.adjugate state.rows initialGrid).work+
      (GeneralPaperBasisPreparationBits.direction model.rat W state.determinant state.adjugate state.rows next).work≤
        16384*(m*((prepare m k).K-1)+1)^2*(W+model.rat (GeneralPaperBasisPreparationWidths.envelope
          (m*((prepare m k).K-1)) (m+1) N (prepare m k).H B)) := by
  have hc := GeneralPaperBasisCacheSize.cache_H k hm dict v S h N betaN initialGrid hj state inv
  have hConstant (i) : (state.rows.read i).constant.natAbs≤m+1 := by
    have hh := GeneralPaperBasisRowSize.rhs_entry hm dict v S h N betaN initialGrid hj state inv i false
    exact hh
  have hSlope (i) : (state.rows.read i).slope.natAbs≤m+1 := by
    have hh := GeneralPaperBasisRowSize.rhs_entry hm dict v S h N betaN initialGrid hj state inv i true
    exact hh
  have hRow := GeneralPaperBasisRowSize.coefficient hm dict v S h N betaN initialGrid hj state inv
  have hJ : binaryWordWidth (j+1)≤W := (binaryWordWidth_mono (show j+1≤m*((prepare m k).K-1)+1 by omega)).trans hDim
  have hw := GeneralPaperBasisPreparationWidths.component_widths j (m*((prepare m k).K-1)) (m+1) N (prepare m k).H B hj
  have hp := (GeneralPaperBasisPreparationBits.point_work model.rat model.monotone W (m+1) N (prepare m k).H B hW hJ hDim
    betaN state.determinant state.adjugate state.rows initialGrid hBeta hc.1 hc.2 hConstant hSlope hRow hGrid).trans
    (Nat.mul_le_mul_left _ (Nat.add_le_add_left (model.monotone hw.1) W))
  have hd := (GeneralPaperBasisPreparationBits.direction_work model.rat model.monotone W (m+1) (prepare m k).H hW hJ hDim
    state.determinant state.adjugate state.rows next hc.1 hc.2 hRow).trans
    (Nat.mul_le_mul_left _ (Nat.add_le_add_left (model.monotone hw.2) W))
  have hp' := hp.trans (phase_scale j (m*((prepare m k).K-1)) W _ hj)
  have hd' := hd.trans (phase_scale j (m*((prepare m k).K-1)) W _ hj)
  nlinarith only [hp',hd']

theorem actual_source_stage {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv) (weights : FixedArrayTable m ℕ)
    (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv) (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool)
    (hW : 1≤W) (hDim : binaryWordWidth (m*((prepare m k).K-1)+1)≤W) :
    let prep := GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b reciprocal
    let v := GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs
    let f := (GeneralPaperProxyClassifier.classify m k b).choice.proxy
    let inputs := GeneralPaperSharedBasisInputs.prepare k prep v f.num f.den reciprocal
    ∀ j (hj : j<m*((prepare m k).K-1)) (state : State j (m*((prepare m k).K-1))),
      Invariant prep.dictionary v (prepare m k).S prep.threshold inputs.controls.N inputs.betaN inputs.initialGrid (Nat.le_of_lt hj) state →
      (GeneralPaperBasisPreparationBits.point model.rat W inputs.controls.N inputs.betaN state.determinant state.adjugate state.rows inputs.initialGrid).work+
        (GeneralPaperBasisPreparationBits.direction model.rat W state.determinant state.adjugate state.rows (next hj)).work≤
          16384*(m*((prepare m k).K-1)+1)^2*(W+model.rat (GeneralPaperBasisPreparationWidths.envelope
            (m*((prepare m k).K-1)) (m+1) inputs.controls.N (prepare m k).H (GeneralPaperSourceBasisGridSize.auxiliaryBound m k))) := by
  dsimp only
  intro j hj state inv
  have hGrid := GeneralPaperSourceBasisGridSize.grid k Qv hm hQv weights hp hs b hb reciprocal
  have hBeta := GeneralPaperSourceBasisGridSize.auxiliary (m:=m) k b hb reciprocal
  exact from_invariant model W k hm _ _ _ _ _ _ _ _ state (Nat.le_of_lt hj) inv hBeta hGrid (next hj) hW hDim

theorem actual_reached_stage {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv) (weights : FixedArrayTable m ℕ)
    (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv) (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool)
    (hW : 1≤W) (hDim : binaryWordWidth (m*((prepare m k).K-1)+1)≤W) (j : ℕ) (hj : j<m*((prepare m k).K-1)) :
    let prep := GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b reciprocal
    let v := GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs
    let f := (GeneralPaperProxyClassifier.classify m k b).choice.proxy
    let inputs := GeneralPaperSharedBasisInputs.prepare k prep v f.num f.den reciprocal
    ∃ state,GeneralPaperBasisController.stages prep.dictionary.label inputs.matrix (prepare m k).S prep.threshold
        inputs.controls.N inputs.betaN inputs.initialGrid j (Nat.le_of_lt hj)=some state ∧
      (GeneralPaperBasisPreparationBits.point model.rat W inputs.controls.N inputs.betaN state.determinant state.adjugate state.rows inputs.initialGrid).work+
        (GeneralPaperBasisPreparationBits.direction model.rat W state.determinant state.adjugate state.rows (next hj)).work≤
          16384*(m*((prepare m k).K-1)+1)^2*(W+model.rat (16384+512*binaryWordWidth inputs.controls.N+
            3072*((prepare m k).d+2)*binaryWordWidth (m+3)+
            2048*binaryWordWidth ((prepare m k).d+m+(prepare m k).K+(prepare m k).S+
              (GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows+2))) := by
  let prep := GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b reciprocal
  let v := GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs
  let f := (GeneralPaperProxyClassifier.classify m k b).choice.proxy
  let inputs := GeneralPaperSharedBasisInputs.prepare k prep v f.num f.den reciprocal
  have hStart := GeneralPaperSourceBasisInputValidity.actual_start k Qv hm hQv weights hp hs b hb reciprocal
  have hn : 0 < inputs.controls.N := (GeneralPaperInitializerSelectedControls.positive m k hm b hb reciprocal).1
  obtain ⟨state,hr,inv⟩ := GeneralPaperBasisControllerSound.stages_valid (GeneralPaperScoreScaleParameters.prepare m k).depth
    prep.dictionary v (GeneralPaperScoreScaleParameters.labels_positive m k) (prepare m k).S prep.threshold inputs.controls.N hn
    (GeneralPaperScoreScaleParameters.score_cap m k) inputs.betaN inputs.initialGrid hStart j (Nat.le_of_lt hj)
  refine ⟨state,?_,?_⟩
  · rw [GeneralPaperSharedBasisInputs.matrix_eq]
    exact hr
  · exact (actual_source_stage model W k Qv hm hQv weights hp hs b hb reciprocal hW hDim j hj state inv).trans
      (Nat.mul_le_mul_left _ (Nat.add_le_add_left (model.monotone
        (GeneralPaperBasisPreparationWidths.paper_envelope m k inputs.controls.N (prepare m k).S
          (GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows)) W))

end Blotto.GeneralPaperBasisPreparationStageBits
