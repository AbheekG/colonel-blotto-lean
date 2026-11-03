import Blotto.GeneralPaperInitializerGridActual

/-! Actual selected source: rounded original grid, one score matrix and the
COMPLETE native basis loop in one bit-priced program. The native rounded
dictionary, shared matrix, state and invariant are preserved. Its source,
N/depth/beta controls and auxiliary numerator are supplied by earlier phases;
their construction, final compiler and full simultaneous-space join remain.
-/
namespace Blotto.GeneralPaperInitializedBasisBits
open GeneralPaperProxyParameters GeneralPaperInitializerSelectedControls GeneralPaperBasisStoredProducts
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 4096

def run {T m K S : ℕ} (model : RationalCostModel) (W scoreDepth : ℕ)
    (prep : GeneralPaperTransferPreparation.Prepared T m K S) (v : RationalFieldSelector m)
    (c : GeneralPaperInitializerParameters.Parameters) (betaN : ℤ) :
    (GeneralPaperDictionary.Dictionary T m K × FixedArrayTable m (GeneralPaperExactScoreDP.Field K) ×
      Option (GeneralPaperBasisState.State (m*(K-1)) (m*(K-1)))) × ℕ :=
  let initialized := GeneralPaperInitializerGridPrice.run model W c.N c.depth prep.dictionary
  let matrix := GeneralPaperScoreMatrixBits.matrixRun model W scoreDepth prep.dictionary v S
  let basis := GeneralPaperBasisControllerBits.stages model W prep.dictionary.label matrix.1 S prep.threshold c.N betaN
    initialized.1.2 (m*(K-1)) (Nat.le_refl _)
  ((initialized.1.1,matrix.1,basis.1),initialized.2+matrix.2+basis.2+40*W)

theorem actual_data {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv)
    (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool) :
    let prep := GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b reciprocal
    let v := GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs
    let f := (GeneralPaperProxyClassifier.classify m k b).choice.proxy
    let inputs := GeneralPaperSharedBasisInputs.prepare k prep v f.num f.den reciprocal
    (run model W (GeneralPaperScoreScaleParameters.prepare m k).depth prep v (controls m k b reciprocal) inputs.betaN).1=
      (GeneralPaperSourceInitializer.initial k Qv hQv weights hp hs b reciprocal,inputs.matrix,GeneralPaperSharedBasisInputs.basis prep inputs) := by
  dsimp only
  have hi := GeneralPaperInitializerGridActual.actual_data model W k Qv hm hQv weights hp hs b hb reciprocal
  have hm := GeneralPaperPreparedBasisBits.actual_matrix model W k Qv hQv weights hp hs b reciprocal
  dsimp only [run]
  rw [hi,hm,GeneralPaperBasisControllerBits.stages_data]
  rfl

def profile (model : RationalCostModel) (W m k Qv N depth : ℕ) : ℕ :=
  GeneralPaperInitializerGridPrice.profile model W N depth (GeneralPaperSourceScoreHeights.anchorHeight m k) m (prepare m k).K+
    GeneralPaperPreparedBasisBits.profile model W m k Qv N+24*W

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
    let c := controls m k b reciprocal
    (run model W (GeneralPaperScoreScaleParameters.prepare m k).depth prep v c inputs.betaN).2≤profile model W m k Qv c.N c.depth := by
  dsimp only
  have hi := GeneralPaperInitializerGridActual.actual_data model W k Qv hm hQv weights hp hs b hb reciprocal
  have hmData := GeneralPaperPreparedBasisBits.actual_matrix model W k Qv hQv weights hp hs b reciprocal
  have hiCost := GeneralPaperInitializerGridActual.actual_work model W k Qv hm hQv weights hp hs b hb reciprocal hW hDim
  have hmCost := GeneralPaperPreparedBasisBits.actual_matrix_work model W k Qv hm hQv weights hp hs b hb reciprocal hW hDim
  have hcCost := GeneralPaperSharedBasisBits.actual_work model W k Qv hm hQv weights hp hs b hb reciprocal hW hDim hIndex hBatch hFinal
  have hControls :
      (GeneralPaperSharedBasisInputs.prepare k (GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b reciprocal)
        (GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs)
        (GeneralPaperProxyClassifier.classify m k b).choice.proxy.num (GeneralPaperProxyClassifier.classify m k b).choice.proxy.den reciprocal).controls.N=
          (controls m k b reciprocal).N := rfl
  dsimp only at hcCost
  rw [hControls] at hcCost
  dsimp only [run]
  rw [hi,hmData]
  change (GeneralPaperInitializerGridPrice.run model W _ _ _).2+_+(GeneralPaperSharedBasisBits.run model W _ _).2+40*W≤_
  unfold profile GeneralPaperPreparedBasisBits.profile
  omega

theorem actual_return {m : ℕ} (model : RationalCostModel) (k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv)
    (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool) :
    let prep := GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b reciprocal
    let v := GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs
    let f := (GeneralPaperProxyClassifier.classify m k b).choice.proxy
    let inputs := GeneralPaperSharedBasisInputs.prepare k prep v f.num f.den reciprocal
    let c := controls m k b reciprocal
    let W := GeneralPaperInitializerGridActual.word m k c.N c.depth
    ∃ state,(run model W (GeneralPaperScoreScaleParameters.prepare m k).depth prep v c inputs.betaN).1=
      (GeneralPaperSourceInitializer.initial k Qv hQv weights hp hs b reciprocal,inputs.matrix,some state) ∧
      GeneralPaperBasisInvariant.Invariant prep.dictionary v (prepare m k).S prep.threshold inputs.controls.N inputs.betaN inputs.initialGrid (Nat.le_refl _) state ∧
      (run model W (GeneralPaperScoreScaleParameters.prepare m k).depth prep v c inputs.betaN).2≤profile model W m k Qv c.N c.depth := by
  dsimp only
  obtain ⟨state,hr,inv⟩ := GeneralPaperSharedBasisInputs.actual_source k Qv hm hQv weights hp hs b hb reciprocal
  have hd := actual_data model (GeneralPaperInitializerGridActual.word m k (controls m k b reciprocal).N (controls m k b reciprocal).depth)
    k Qv hm hQv weights hp hs b hb reciprocal
  dsimp only at hd
  rw [hr] at hd
  have hw := GeneralPaperInitializerGridActual.capacities m k (controls m k b reciprocal).N (controls m k b reciprocal).depth
  exact ⟨state,hd,inv,actual_work model _ k Qv hm hQv weights hp hs b hb reciprocal hw.1 hw.2.1 hw.2.2.1 hw.2.2.2.1 hw.2.2.2.2.1⟩

end Blotto.GeneralPaperInitializedBasisBits
