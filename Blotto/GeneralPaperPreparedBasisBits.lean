import Blotto.GeneralPaperSourceAlphabetLower

/-! Build the bit-priced score matrix ONCE and pass that stored value to
the complete native basis loop. The result retains the matrix for final
rechecks. Source, initializer and original-grid construction are earlier
phases. Local capacities are derived by a concrete logarithmic word; the
global source/reference/space and original-input joins remain separate.
-/
namespace Blotto.GeneralPaperPreparedBasisBits
open GeneralPaperProxyParameters GeneralPaperBasisStoredProducts
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 4096

def run {T m K S : ℕ} (model : RationalCostModel) (W depth : ℕ)
    (prep : GeneralPaperTransferPreparation.Prepared T m K S) (v : RationalFieldSelector m)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m K) :
    (FixedArrayTable m (GeneralPaperExactScoreDP.Field K) × Option (GeneralPaperBasisState.State (m*(K-1)) (m*(K-1)))) × ℕ :=
  let matrix := GeneralPaperScoreMatrixBits.matrixRun model W depth prep.dictionary v S
  let basis := GeneralPaperBasisControllerBits.stages model W prep.dictionary.label matrix.1 S prep.threshold
    inputs.controls.N inputs.betaN inputs.initialGrid (m*(K-1)) (Nat.le_refl _)
  ((matrix.1,basis.1),matrix.2+basis.2+16*W)

theorem data {T m K S : ℕ} (model : RationalCostModel) (W depth : ℕ)
    (prep : GeneralPaperTransferPreparation.Prepared T m K S) (v : RationalFieldSelector m)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m K)
    (hMatrix : (GeneralPaperScoreMatrixBits.matrixRun model W depth prep.dictionary v S).1=inputs.matrix) :
    (run model W depth prep v inputs).1=(inputs.matrix,GeneralPaperSharedBasisInputs.basis prep inputs) := by
  simp only [run,hMatrix,GeneralPaperBasisControllerBits.stages_data]
  rfl

theorem actual_matrix {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv) (b : ℝ) (reciprocal : Bool) :
    let prep := GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b reciprocal
    let v := GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs
    let f := (GeneralPaperProxyClassifier.classify m k b).choice.proxy
    let inputs := GeneralPaperSharedBasisInputs.prepare k prep v f.num f.den reciprocal
    (GeneralPaperScoreMatrixBits.matrixRun model W (GeneralPaperScoreScaleParameters.prepare m k).depth prep.dictionary v (prepare m k).S).1=inputs.matrix := by
  dsimp only
  rw [GeneralPaperSharedBasisInputs.matrix_eq]
  exact GeneralPaperScoreMatrixEnvelope.matrix_data_native model W _ _ _ _
    (GeneralPaperScoreScaleParameters.labels_positive m k) (GeneralPaperScoreScaleParameters.score_cap m k)

def matrixProfile (model : RationalCostModel) (W m k Qv : ℕ) : ℕ :=
  GeneralPaperScoreMatrixBits.matrixProfile model W (binaryWordWidth Qv) (GeneralPaperSourceScoreHeights.anchorHeight m k)
    (GeneralPaperScoreScaleParameters.prepare m k).depth m (prepare m k).K

theorem actual_matrix_work {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv)
    (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool) (hW : 1≤W)
    (hDim : binaryWordWidth (m*((prepare m k).K-1)+3)≤W) :
    let prep := GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b reciprocal
    let v := GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs
    (GeneralPaperScoreMatrixBits.matrixRun model W (GeneralPaperScoreScaleParameters.prepare m k).depth prep.dictionary v (prepare m k).S).2≤
      matrixProfile model W m k Qv := by
  dsimp only
  have hc := GeneralPaperBasisBitEnvelope.index_capacities m k W hm hDim
  exact GeneralPaperScoreMatrixBits.matrix_work model W _ _ _ _ _ _
    (GeneralPaperScoreScaleParameters.labels_positive m k) (GeneralPaperScoreScaleParameters.score_cap m k)
    (GeneralPaperSourceScoreHeights.value_height Qv hQv weights hp hs)
    (GeneralPaperSourceScoreHeights.prepared_anchors k Qv hQv weights hp hs b hb reciprocal) hW hc.2.1 hc.2.2

def profile (model : RationalCostModel) (W m k Qv N : ℕ) : ℕ := matrixProfile model W m k Qv+
  GeneralPaperBasisControllerBits.profile (GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows
    m (prepare m k).K (prepare m k).S W
    (model.rat (GeneralPaperBasisBitEnvelope.width m k N (prepare m k).S (GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows))+16*W

theorem actual_work {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv)
    (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool) (hW : 1≤W)
    (hDim : binaryWordWidth (m*((prepare m k).K-1)+3)≤W) (hIndex : binaryWordWidth ((prepare m k).S+2)≤W)
    (hBatch : binaryWordWidth (((prepare m k).S+1)*((prepare m k).K*(prepare m k).K)+3)≤W)
    (hFinal : binaryWordWidth ((prepare m k).S+4)≤W) :
    let prep := GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b reciprocal
    let v := GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs
    let f := (GeneralPaperProxyClassifier.classify m k b).choice.proxy
    let inputs := GeneralPaperSharedBasisInputs.prepare k prep v f.num f.den reciprocal
    (run model W (GeneralPaperScoreScaleParameters.prepare m k).depth prep v inputs).2≤profile model W m k Qv inputs.controls.N := by
  dsimp only
  have hMat := actual_matrix model W k Qv hQv weights hp hs b reciprocal
  have hmCost := actual_matrix_work model W k Qv hm hQv weights hp hs b hb reciprocal hW hDim
  have hc := GeneralPaperSharedBasisBits.actual_work model W k Qv hm hQv weights hp hs b hb reciprocal hW hDim hIndex hBatch hFinal
  dsimp only [run]
  rw [hMat]
  change _+ (GeneralPaperSharedBasisBits.run model W _ _).2+16*W≤_
  unfold profile
  omega

theorem profile_bound (model : RationalCostModel) (W m k Qv N : ℕ) :
    profile model W m k Qv N≤
      512*(m+1)*((prepare m k).K+1)*((GeneralPaperScoreScaleParameters.prepare m k).depth+1)*
        (W+model.rat (GeneralPaperScoreMatrixEnvelope.width (binaryWordWidth Qv) (GeneralPaperSourceScoreHeights.anchorHeight m k)
          (GeneralPaperScoreScaleParameters.prepare m k).depth (prepare m k).K))+
      262144*(m*((prepare m k).K-1)+3)^3*(W+model.rat (GeneralPaperBasisBitEnvelope.width m k N (prepare m k).S
        (GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows))+
      (m*((prepare m k).K-1))*GeneralPaperEndpointPriceControl.profile (GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows
        m (prepare m k).K (prepare m k).S W (model.rat (GeneralPaperBasisBitEnvelope.width m k N (prepare m k).S
          (GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows))+16*W := by
  have hm := GeneralPaperScoreMatrixEnvelope.matrix_profile model W (binaryWordWidth Qv) (GeneralPaperSourceScoreHeights.anchorHeight m k)
    (GeneralPaperScoreScaleParameters.prepare m k).depth m (prepare m k).K
  have hc := GeneralPaperBasisControllerBits.profile_bound (GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows
    m (prepare m k).K (prepare m k).S W (model.rat (GeneralPaperBasisBitEnvelope.width m k N (prepare m k).S
      (GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows))
  unfold profile matrixProfile
  omega

theorem actual_return {m : ℕ} (model : RationalCostModel) (k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv)
    (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool) :
    let W := GeneralPaperScoreBasisControls.word m k
    let prep := GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b reciprocal
    let v := GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs
    let f := (GeneralPaperProxyClassifier.classify m k b).choice.proxy
    let inputs := GeneralPaperSharedBasisInputs.prepare k prep v f.num f.den reciprocal
    ∃ state,(run model W (GeneralPaperScoreScaleParameters.prepare m k).depth prep v inputs).1=(inputs.matrix,some state) ∧
      GeneralPaperBasisInvariant.Invariant prep.dictionary v (prepare m k).S prep.threshold inputs.controls.N inputs.betaN inputs.initialGrid (Nat.le_refl _) state ∧
      (run model W (GeneralPaperScoreScaleParameters.prepare m k).depth prep v inputs).2≤profile model W m k Qv inputs.controls.N := by
  dsimp only
  obtain ⟨state,hr,inv⟩ := GeneralPaperSharedBasisInputs.actual_source k Qv hm hQv weights hp hs b hb reciprocal
  have hd := data model (GeneralPaperScoreBasisControls.word m k) (GeneralPaperScoreScaleParameters.prepare m k).depth
    _ _ _ (actual_matrix model _ k Qv hQv weights hp hs b reciprocal)
  rw [hr] at hd
  have hw := GeneralPaperScoreBasisControls.capacities m k
  exact ⟨state,hd,inv,actual_work model _ k Qv hm hQv weights hp hs b hb reciprocal hw.1 hw.2.1 hw.2.2.1 hw.2.2.2.1 hw.2.2.2.2.1⟩

end Blotto.GeneralPaperPreparedBasisBits
