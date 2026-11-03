import Blotto.GeneralPaperInitializedBasisBits

/-! The same rounded-grid/matrix/full-basis program in unit arithmetic.
Both indexed matrix levels and initializer levels use unit index prices.
The arithmetic theorem has no input-encoding width or word-capacity premise.
Bit-program comparisons below are erased exact-data proofs, not executed
bit calls in the arithmetic program. Source/control construction, final
compiler and the full simultaneous working-space join remain separate.
-/
namespace Blotto.GeneralPaperInitializedBasisWork
open GeneralPaperProxyParameters GeneralPaperInitializerSelectedControls GeneralPaperBasisStoredProducts
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 4096

def run {T m K S : ℕ} (scoreDepth : ℕ) (prep : GeneralPaperTransferPreparation.Prepared T m K S)
    (v : RationalFieldSelector m) (c : GeneralPaperInitializerParameters.Parameters) (betaN : ℤ) :
    (GeneralPaperDictionary.Dictionary T m K × FixedArrayTable m (GeneralPaperExactScoreDP.Field K) ×
      Option (GeneralPaperBasisState.State (m*(K-1)) (m*(K-1)))) × ℕ :=
  let initialized := GeneralPaperInitializerGridPrice.unit c.N c.depth prep.dictionary
  let matrix := GeneralPaperScoreMatrixUnit.run scoreDepth prep.dictionary v S
  let basis := GeneralPaperBasisControllerWork.stages prep.dictionary.label matrix.1 S prep.threshold c.N betaN
    initialized.1.2 (m*(K-1)) (Nat.le_refl _)
  ((initialized.1.1,matrix.1,basis.1),initialized.2+matrix.2+basis.2+40)

theorem data {T m K S : ℕ} (model : RationalCostModel) (W scoreDepth : ℕ)
    (prep : GeneralPaperTransferPreparation.Prepared T m K S) (v : RationalFieldSelector m)
    (c : GeneralPaperInitializerParameters.Parameters) (betaN : ℤ) (hK : 0<K) (hCap : S<2^scoreDepth) :
    (run scoreDepth prep v c betaN).1=(GeneralPaperInitializedBasisBits.run model W scoreDepth prep v c betaN).1 := by
  simp only [run,GeneralPaperInitializedBasisBits.run,GeneralPaperInitializerGridPrice.data_unit,
    GeneralPaperScoreMatrixEnvelope.matrix_data_native model W scoreDepth prep.dictionary v S hK hCap,
    GeneralPaperScoreMatrixUnit.data,GeneralPaperBasisControllerWork.stages_data,GeneralPaperBasisControllerBits.stages_data]

theorem actual_data {m : ℕ} (k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv) (weights : FixedArrayTable m ℕ)
    (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv) (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool) :
    let prep := GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b reciprocal
    let v := GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs
    let f := (GeneralPaperProxyClassifier.classify m k b).choice.proxy
    let inputs := GeneralPaperSharedBasisInputs.prepare k prep v f.num f.den reciprocal
    (run (GeneralPaperScoreScaleParameters.prepare m k).depth prep v (controls m k b reciprocal) inputs.betaN).1=
      (GeneralPaperSourceInitializer.initial k Qv hQv weights hp hs b reciprocal,inputs.matrix,GeneralPaperSharedBasisInputs.basis prep inputs) := by
  dsimp only
  exact (data RationalCostModel.schoolbook 1 _ _ _ _ _ (GeneralPaperScoreScaleParameters.labels_positive m k)
    (GeneralPaperScoreScaleParameters.score_cap m k)).trans
    (GeneralPaperInitializedBasisBits.actual_data RationalCostModel.schoolbook 1 k Qv hm hQv weights hp hs b hb reciprocal)

def profile (T m K S scoreDepth initialDepth : ℕ) : ℕ :=
  128*(m+1)*(K+1)*(initialDepth+1)+1024*(m*(K-1)+m+1)+16+
    256*(m+1)*(K+1)*(scoreDepth+1)+72+(m*(K-1))*(GeneralPaperBasisStepWork.profile T m K S+24)+40

theorem actual_work {m : ℕ} (k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv) (weights : FixedArrayTable m ℕ)
    (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv) (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool) :
    let prep := GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b reciprocal
    let v := GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs
    let f := (GeneralPaperProxyClassifier.classify m k b).choice.proxy
    let inputs := GeneralPaperSharedBasisInputs.prepare k prep v f.num f.den reciprocal
    let c := controls m k b reciprocal
    (run (GeneralPaperScoreScaleParameters.prepare m k).depth prep v c inputs.betaN).2≤
      profile (GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows m (prepare m k).K (prepare m k).S
        (GeneralPaperScoreScaleParameters.prepare m k).depth c.depth := by
  dsimp only
  have hiBits := GeneralPaperInitializerGridActual.actual_data RationalCostModel.schoolbook 1 k Qv hm hQv weights hp hs b hb reciprocal
  have hiUnit := GeneralPaperInitializerGridPrice.data_unit RationalCostModel.schoolbook 1
    (controls m k b reciprocal).N (controls m k b reciprocal).depth
    (GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b reciprocal).dictionary
  have hi := hiUnit.symm.trans hiBits
  have hmBits := GeneralPaperPreparedBasisBits.actual_matrix RationalCostModel.schoolbook 1 k Qv hQv weights hp hs b reciprocal
  have hmUnit := GeneralPaperScoreMatrixUnit.data (GeneralPaperScoreScaleParameters.prepare m k).depth
    (GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b reciprocal).dictionary
    (GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs) (prepare m k).S
  have hmNative := GeneralPaperScoreMatrixEnvelope.matrix_data_native RationalCostModel.schoolbook 1
    (GeneralPaperScoreScaleParameters.prepare m k).depth
    (GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b reciprocal).dictionary
    (GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs) (prepare m k).S
    (GeneralPaperScoreScaleParameters.labels_positive m k) (GeneralPaperScoreScaleParameters.score_cap m k)
  have hmData := hmUnit.trans (hmNative.symm.trans hmBits)
  have hiCost := GeneralPaperInitializerGridPrice.unit_work (controls m k b reciprocal).N (controls m k b reciprocal).depth
    (GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b reciprocal).dictionary
  have hmCost := GeneralPaperScoreMatrixUnit.work (GeneralPaperScoreScaleParameters.prepare m k).depth
    (GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b reciprocal).dictionary
    (GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs) (prepare m k).S
  have hcCost := GeneralPaperSharedBasisWork.actual_work k Qv hm hQv weights hp hs b hb reciprocal
  dsimp only [run]
  rw [hi,hmData]
  change (GeneralPaperInitializerGridPrice.unit _ _ _).2+_+(GeneralPaperSharedBasisWork.run _ _).2+40≤_
  unfold profile
  omega

theorem actual_return {m : ℕ} (k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv) (weights : FixedArrayTable m ℕ)
    (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv) (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool) :
    let prep := GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b reciprocal
    let v := GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs
    let f := (GeneralPaperProxyClassifier.classify m k b).choice.proxy
    let inputs := GeneralPaperSharedBasisInputs.prepare k prep v f.num f.den reciprocal
    let c := controls m k b reciprocal
    ∃ state,(run (GeneralPaperScoreScaleParameters.prepare m k).depth prep v c inputs.betaN).1=
      (GeneralPaperSourceInitializer.initial k Qv hQv weights hp hs b reciprocal,inputs.matrix,some state) ∧
      GeneralPaperBasisInvariant.Invariant prep.dictionary v (prepare m k).S prep.threshold inputs.controls.N inputs.betaN inputs.initialGrid (Nat.le_refl _) state ∧
      (run (GeneralPaperScoreScaleParameters.prepare m k).depth prep v c inputs.betaN).2≤
        profile (GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows m (prepare m k).K (prepare m k).S
          (GeneralPaperScoreScaleParameters.prepare m k).depth c.depth := by
  dsimp only
  obtain ⟨state,hr,inv⟩ := GeneralPaperSharedBasisInputs.actual_source k Qv hm hQv weights hp hs b hb reciprocal
  have hd := actual_data k Qv hm hQv weights hp hs b hb reciprocal
  dsimp only at hd
  rw [hr] at hd
  exact ⟨state,hd,inv,actual_work k Qv hm hQv weights hp hs b hb reciprocal⟩

end Blotto.GeneralPaperInitializedBasisWork
