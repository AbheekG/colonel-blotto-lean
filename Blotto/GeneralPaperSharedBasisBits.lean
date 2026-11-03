import Blotto.GeneralPaperBasisControllerBits

/-! The selected source's actual shared-matrix basis loop has the complete
bit controller price, with all start/grid/auxiliary premises derived. This
does not price source/initializer/grid or one-time matrix preparation, nor
discharge the full global reference/control capacities or working storage.
-/
namespace Blotto.GeneralPaperSharedBasisBits
open RationalOrderCell GeneralPaperProxyParameters GeneralPaperBasisStoredProducts
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 4096

def run {T m K S : ℕ} (model : RationalCostModel) (W : ℕ) (prep : GeneralPaperTransferPreparation.Prepared T m K S)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m K) : Option (GeneralPaperBasisState.State (m*(K-1)) (m*(K-1))) × ℕ :=
  GeneralPaperBasisControllerBits.stages model W prep.dictionary.label inputs.matrix S prep.threshold inputs.controls.N inputs.betaN
    inputs.initialGrid (m*(K-1)) (Nat.le_refl _)

theorem data {T m K S : ℕ} (model : RationalCostModel) (W : ℕ) (prep : GeneralPaperTransferPreparation.Prepared T m K S)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m K) :
    (run model W prep inputs).1=GeneralPaperSharedBasisInputs.basis prep inputs := GeneralPaperBasisControllerBits.stages_data _ _ _ _ _ _ _ _ _ _ _

theorem actual_work {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv) (weights : FixedArrayTable m ℕ)
    (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv) (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool)
    (hW : 1≤W) (hDim : binaryWordWidth (m*((prepare m k).K-1)+3)≤W)
    (hIndex : binaryWordWidth ((prepare m k).S+2)≤W)
    (hBatch : binaryWordWidth (((prepare m k).S+1)*((prepare m k).K*(prepare m k).K)+3)≤W)
    (hFinal : binaryWordWidth ((prepare m k).S+4)≤W) :
    let prep := GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b reciprocal
    let v := GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs
    let f := (GeneralPaperProxyClassifier.classify m k b).choice.proxy
    let inputs := GeneralPaperSharedBasisInputs.prepare k prep v f.num f.den reciprocal
    (run model W prep inputs).2≤GeneralPaperBasisControllerBits.profile
      (GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows m (prepare m k).K (prepare m k).S W
      (model.rat (GeneralPaperBasisBitEnvelope.width m k inputs.controls.N (prepare m k).S
        (GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows)) := by
  dsimp only
  rw [run,GeneralPaperSharedBasisInputs.matrix_eq]
  exact GeneralPaperBasisControllerBits.stages_work model W k hm (GeneralPaperScoreScaleParameters.prepare m k).depth _ _ _ _ _
    (GeneralPaperInitializerSelectedControls.positive m k hm b hb reciprocal).1 (GeneralPaperScoreScaleParameters.score_cap m k)
    _ _ (GeneralPaperSourceBasisGridSize.auxiliary (m:=m) k b hb reciprocal)
    (GeneralPaperSourceBasisGridSize.grid k Qv hm hQv weights hp hs b hb reciprocal)
    (GeneralPaperSourceBasisInputValidity.actual_start k Qv hm hQv weights hp hs b hb reciprocal)
    hW hDim hIndex hBatch hFinal _ (Nat.le_refl _)

theorem actual_return {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv) (weights : FixedArrayTable m ℕ)
    (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv) (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool)
    (hW : 1≤W) (hDim : binaryWordWidth (m*((prepare m k).K-1)+3)≤W)
    (hIndex : binaryWordWidth ((prepare m k).S+2)≤W)
    (hBatch : binaryWordWidth (((prepare m k).S+1)*((prepare m k).K*(prepare m k).K)+3)≤W)
    (hFinal : binaryWordWidth ((prepare m k).S+4)≤W) :
    let prep := GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b reciprocal
    let v := GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs
    let f := (GeneralPaperProxyClassifier.classify m k b).choice.proxy
    let inputs := GeneralPaperSharedBasisInputs.prepare k prep v f.num f.den reciprocal
    ∃ state,(run model W prep inputs).1=some state ∧
      GeneralPaperBasisInvariant.Invariant prep.dictionary v (prepare m k).S prep.threshold inputs.controls.N inputs.betaN inputs.initialGrid (Nat.le_refl _) state ∧
      (run model W prep inputs).2≤GeneralPaperBasisControllerBits.profile
        (GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows m (prepare m k).K (prepare m k).S W
        (model.rat (GeneralPaperBasisBitEnvelope.width m k inputs.controls.N (prepare m k).S
          (GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows)) := by
  dsimp only
  obtain ⟨state,hr,inv⟩ := GeneralPaperSharedBasisInputs.actual_source k Qv hm hQv weights hp hs b hb reciprocal
  exact ⟨state,(data model W _ _).trans hr,inv,actual_work model W k Qv hm hQv weights hp hs b hb reciprocal hW hDim hIndex hBatch hFinal⟩

end Blotto.GeneralPaperSharedBasisBits
