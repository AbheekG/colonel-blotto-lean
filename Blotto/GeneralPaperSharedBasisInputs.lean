import Blotto.GeneralPaperFinalPolytopeCheck

/-! Shared native initializer/grid and score-matrix preparation. The
basis loop and both final rechecks read this SAME stored matrix. No source
trajectory, strict threshold, matrix or auxiliary point is replayed.
-/
namespace Blotto.GeneralPaperSharedBasisInputs
open RationalOrderCell GeneralPaperBasisStoredProducts GeneralPaperBasisState GeneralPaperProxyParameters
set_option autoImplicit false
set_option maxHeartbeats 3500000

structure Inputs (T m K : ℕ) where
  controls : GeneralPaperInitializerParameters.Parameters
  betaN : ℤ
  initialGrid : Vector (m*(K-1))
  matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K)

def prepare {T m : ℕ} (k : ℕ)
    (prep : GeneralPaperTransferPreparation.Prepared T m (GeneralPaperProxyParameters.prepare m k).K (GeneralPaperProxyParameters.prepare m k).S)
    (v : RationalFieldSelector m) (p q : ℕ) (reciprocal : Bool) : Inputs T m (GeneralPaperProxyParameters.prepare m k).K :=
  let c := GeneralPaperInitializerParameters.prepare m (GeneralPaperProxyParameters.prepare m k).H p q reciprocal
  let init := GeneralPaperInitializerDictionary.build prep.dictionary c.N c.depth
  let point := fun a : Variable m (GeneralPaperProxyParameters.prepare m k).K =>
    init.anchor a.1 (GeneralPaperTransferPolytopePoint.positiveLabel a.2)
  let grid := GeneralPaperBasisGridInputs.grid c.N point
  let matrix := GeneralPaperScoreMatrixWork.matrixRun (GeneralPaperScoreScaleParameters.prepare m k).depth
    prep.dictionary v (GeneralPaperProxyParameters.prepare m k).S
  ⟨c,GeneralPaperBasisGridInputs.auxiliaryNumerator m (GeneralPaperProxyParameters.prepare m k).H p q reciprocal,grid,matrix.1⟩

def basis {T m K S : ℕ} (prep : GeneralPaperTransferPreparation.Prepared T m K S) (inputs : Inputs T m K) :
    Option (State (m*(K-1)) (m*(K-1))) :=
  GeneralPaperBasisController.stages prep.dictionary.label inputs.matrix S prep.threshold inputs.controls.N inputs.betaN
    inputs.initialGrid (m*(K-1)) (Nat.le_refl _)

theorem matrix_eq {T m : ℕ} (k : ℕ)
    (prep : GeneralPaperTransferPreparation.Prepared T m (GeneralPaperProxyParameters.prepare m k).K (GeneralPaperProxyParameters.prepare m k).S)
    (v : RationalFieldSelector m) (p q : ℕ) (reciprocal : Bool) :
    (prepare k prep v p q reciprocal).matrix=
      (GeneralPaperScoreMatrixWork.matrixRun (GeneralPaperScoreScaleParameters.prepare m k).depth prep.dictionary v
        (GeneralPaperProxyParameters.prepare m k).S).1 := rfl

theorem basis_eq {T m : ℕ} (k : ℕ)
    (prep : GeneralPaperTransferPreparation.Prepared T m (GeneralPaperProxyParameters.prepare m k).K (GeneralPaperProxyParameters.prepare m k).S)
    (v : RationalFieldSelector m) (p q : ℕ) (reciprocal : Bool) :
    basis prep (prepare k prep v p q reciprocal)=GeneralPaperSourceBasis.fromPrepared k prep v p q reciprocal := rfl

theorem actual_source {m : ℕ} (k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv) (weights : FixedArrayTable m ℕ)
    (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv) (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool) :
    let prep := GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b reciprocal
    let f := (GeneralPaperProxyClassifier.classify m k b).choice.proxy
    let inputs := prepare k prep (GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs) f.num f.den reciprocal
    ∃ state,basis prep inputs=some state ∧
      GeneralPaperBasisInvariant.Invariant prep.dictionary (GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs)
        (GeneralPaperProxyParameters.prepare m k).S prep.threshold inputs.controls.N inputs.betaN inputs.initialGrid (Nat.le_refl _) state :=
  GeneralPaperSourceBasis.run_valid k Qv hm hQv weights hp hs b hb reciprocal

end Blotto.GeneralPaperSharedBasisInputs
