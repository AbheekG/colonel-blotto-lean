import Blotto.GeneralPaperBasisAppendRows

/-! The actual original blocker derivative preserves the exact stored
basis invariant for the actual appended original rows. No positive ray
length is required.
-/
namespace Blotto.GeneralPaperBasisAppendCache
open RationalOrderCell GeneralPaperAffineConstraintRows GeneralPaperBasisStoredProducts
open GeneralPaperBasisFreshRHS GeneralPaperBasisDenseRow GeneralPaperBasisOriginalDirection
open GeneralPaperBasisIntegerCasts GeneralPaperBasisStoredCorrect
set_option autoImplicit false
set_option maxHeartbeats 3500000

theorem original_positive {m K j : ℕ} (D : ℤ) (hD : D≠0) (A : IntMatrix j)
    (rows : Rows j (m*(K-1))) (next : Fin (m*(K-1))) (hNext : next.val=j)
    (hj : j≤m*(K-1)) (hNew : j+1≤m*(K-1)) (hValid : Valid D A (minor rows hj))
    (r : Row (Variable m K))
    (hPositive : 0<r.linear.evaluate
      (fun v => (reader (GeneralPaperBasisDirection.run D A rows next).velocity v:ℝ))) :
    let step := GeneralPaperBasisStoredStep.run D A (GeneralPaperBasisDirection.columnRun rows next).1
      (rowPrefix (build r) hj) ((build r).coefficients.read next)
    step.determinant≠0 ∧ Valid step.determinant step.adjugate
      (minor (GeneralPaperBasisAppendRows.append rows (build r)) hNew) := by
  rw [schur_identity D A rows next hNext hj r] at hPositive
  have hDet : (minor rows hj).det≠0 := by rw [←hValid.1]; exact hD
  have hh := GeneralPaperBasisPositiveUpdate.stored_from_positive D A (minor rows hj)
    (GeneralPaperBasisDirection.columnRun rows next).1 (rowPrefix (build r) hj)
    ((build r).coefficients.read next) hValid hDet (GeneralPaperBasisDirectionSound.solved D A rows next)
    (GeneralPaperBasisDirectionSound.solved_system D hD A rows next hj hValid) hPositive
  rw [←GeneralPaperBasisAppendRows.minor_border rows (build r) hj hNew next hNext] at hh
  exact hh

end Blotto.GeneralPaperBasisAppendCache
