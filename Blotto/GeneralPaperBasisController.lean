import Blotto.GeneralPaperBasisStepSound

/-! The actual d-stage original-basis controller. The score matrix is
prepared once, and each stage retains only its original row coefficients
and exact integer determinant/adjugate cache. Stage count zero is allowed.
-/
namespace Blotto.GeneralPaperBasisController
open RationalOrderCell GeneralPaperBasisStoredProducts GeneralPaperBasisState
set_option autoImplicit false

def stages {T m K : ℕ} (labels : Fin T → Fin m → Fin K)
    (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K)) (S h N : ℕ) (betaN : ℤ)
    (initialGrid : Vector (m*(K-1))) : (j : ℕ) → j≤m*(K-1) → Option (State j (m*(K-1)))
  | 0,_ => some (initial (m*(K-1)))
  | j+1,hj =>
    (stages labels matrix S h N betaN initialGrid j (Nat.le_trans (Nat.le_succ j) hj)).bind
      (fun state => step labels matrix S h N betaN initialGrid state (Nat.lt_of_succ_le hj))

def run {T m K : ℕ} (scoreDepth : ℕ) (dict : GeneralPaperDictionary.Dictionary T m K)
    (v : RationalFieldSelector m) (S h N : ℕ) (betaN : ℤ) (initialGrid : Vector (m*(K-1))) :
    Option (State (m*(K-1)) (m*(K-1))) :=
  let matrix := GeneralPaperScoreMatrixWork.matrixRun scoreDepth dict v S
  stages dict.label matrix.1 S h N betaN initialGrid (m*(K-1)) (Nat.le_refl _)

end Blotto.GeneralPaperBasisController
