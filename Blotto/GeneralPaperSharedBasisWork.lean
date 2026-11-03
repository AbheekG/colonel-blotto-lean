import Blotto.GeneralPaperSourceBasisInputValidity

/-! Price the actual shared-matrix basis call. Its prepared source,
initializer/grid and score matrix are reused; their construction prices
belong to the surrounding preparation, not a second controller execution.
The actual selected source discharges the controller's start premises.
-/
namespace Blotto.GeneralPaperSharedBasisWork
open RationalOrderCell GeneralPaperProxyParameters GeneralPaperBasisStoredProducts
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 7000000
set_option maxRecDepth 4096

def run {T m K S : ℕ} (prep : GeneralPaperTransferPreparation.Prepared T m K S)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m K) : Option (GeneralPaperBasisState.State (m*(K-1)) (m*(K-1))) × ℕ :=
  GeneralPaperBasisControllerWork.stages prep.dictionary.label inputs.matrix S prep.threshold inputs.controls.N inputs.betaN
    inputs.initialGrid (m*(K-1)) (Nat.le_refl _)

theorem data {T m K S : ℕ} (prep : GeneralPaperTransferPreparation.Prepared T m K S)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m K) :
    (run prep inputs).1=GeneralPaperSharedBasisInputs.basis prep inputs := GeneralPaperBasisControllerWork.stages_data _ _ _ _ _ _ _ _ _

theorem actual_work {m : ℕ} (k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv) (weights : FixedArrayTable m ℕ)
    (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv) (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool) :
    let prep := GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b reciprocal
    let v := GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs
    let f := (GeneralPaperProxyClassifier.classify m k b).choice.proxy
    let inputs := GeneralPaperSharedBasisInputs.prepare k prep v f.num f.den reciprocal
    (run prep inputs).2≤72+(m*((prepare m k).K-1))*(GeneralPaperBasisStepWork.profile
      (GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows m (prepare m k).K (prepare m k).S+24) := by
  dsimp only
  rw [run,GeneralPaperSharedBasisInputs.matrix_eq]
  exact GeneralPaperBasisControllerWork.stages_work k hm (GeneralPaperScoreScaleParameters.prepare m k).depth _ _
    (GeneralPaperScoreScaleParameters.labels_positive m k) _ _ _
    (GeneralPaperInitializerSelectedControls.positive m k hm b hb reciprocal).1 (GeneralPaperScoreScaleParameters.score_cap m k)
    _ _ (GeneralPaperSourceBasisInputValidity.actual_start k Qv hm hQv weights hp hs b hb reciprocal) _ (Nat.le_refl _)

theorem actual_return {m : ℕ} (k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv) (weights : FixedArrayTable m ℕ)
    (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv) (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool) :
    let prep := GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b reciprocal
    let v := GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs
    let f := (GeneralPaperProxyClassifier.classify m k b).choice.proxy
    let inputs := GeneralPaperSharedBasisInputs.prepare k prep v f.num f.den reciprocal
    ∃ state,(run prep inputs).1=some state ∧
      GeneralPaperBasisInvariant.Invariant prep.dictionary v (prepare m k).S prep.threshold inputs.controls.N inputs.betaN
        inputs.initialGrid (Nat.le_refl _) state ∧
      (run prep inputs).2≤72+(m*((prepare m k).K-1))*(GeneralPaperBasisStepWork.profile
        (GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows m (prepare m k).K (prepare m k).S+24) := by
  dsimp only
  obtain ⟨state,hr,inv⟩ := GeneralPaperSharedBasisInputs.actual_source k Qv hm hQv weights hp hs b hb reciprocal
  exact ⟨state,(data _ _).trans hr,inv,actual_work k Qv hm hQv weights hp hs b hb reciprocal⟩


theorem profile_bound (T m K S : ℕ) (hK : 2≤K) :
    72+(m*(K-1))*(GeneralPaperBasisStepWork.profile T m K S+24)≤8192*(m*(K-1)+3)^3+
      (m*(K-1))*GeneralPaperEndpointPriceControl.profile T m K S 1 1 := by
  have hh := GeneralPaperBasisControllerWork.profile_bound 0 T m K S hK
  unfold GeneralPaperBasisControllerWork.profile at hh
  omega

theorem actual_paper_bound {m : ℕ} (k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv) (weights : FixedArrayTable m ℕ)
    (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv) (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool) :
    let prep := GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b reciprocal
    let v := GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs
    let f := (GeneralPaperProxyClassifier.classify m k b).choice.proxy
    let inputs := GeneralPaperSharedBasisInputs.prepare k prep v f.num f.den reciprocal
    (run prep inputs).2≤8192*(m*((prepare m k).K-1)+3)^3+
      (m*((prepare m k).K-1))*GeneralPaperEndpointPriceControl.profile
        (GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows m (prepare m k).K (prepare m k).S 1 1 := by
  have hK : 2≤(prepare m k).K := by
    rw [(GeneralPaperProxyParameters.data m k).1,GeneralPaperScoreScaleParameters.label_power]
    exact Nat.one_lt_pow (by omega : 7+k≠0) (by decide : 1<(2:ℕ))
  exact (actual_work k Qv hm hQv weights hp hs b hb reciprocal).trans (profile_bound _ m _ _ hK)

end Blotto.GeneralPaperSharedBasisWork
