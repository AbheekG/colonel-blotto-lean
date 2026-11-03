import Blotto.GeneralPaperBasisFull

/-! Cubic source arithmetic for the actually executed fresh point,
direction and cached integer update components. This excludes the ray
search and the still separate row/append/controller and bit/space ledgers.
-/
namespace Blotto.GeneralPaperBasisSolveLedger
open GeneralPaperBasisStoredProducts GeneralPaperBasisState GeneralPaperBasisDenseRow
open GeneralPaperBasisOriginalDirection
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 3500000

def componentWork {j d : ℕ} (N : ℕ) (betaN : ℤ) (initialGrid : Vector d) (state : State j d)
    (hj : j<d) (new : Dense d) : ℕ :=
  (GeneralPaperBasisFreshPoint.run N betaN state.determinant state.adjugate state.rows initialGrid).work+
    (GeneralPaperBasisDirection.run state.determinant state.adjugate state.rows (next hj)).work+
      (GeneralPaperBasisStoredStep.run state.determinant state.adjugate
        (GeneralPaperBasisDirection.columnRun state.rows (next hj)).1 (rowPrefix new (Nat.le_of_lt hj))
        (new.coefficients.read (next hj))).work

theorem stage_work {j d : ℕ} (N : ℕ) (betaN : ℤ) (initialGrid : Vector d) (state : State j d)
    (hj : j<d) (new : Dense d) : componentWork N betaN initialGrid state hj new≤4096*(d+1)^2 := by
  have hp := GeneralPaperBasisFreshPoint.work N betaN state.determinant state.adjugate state.rows initialGrid
  have hv := GeneralPaperBasisDirection.work state.determinant state.adjugate state.rows (next hj)
  have hu := GeneralPaperBasisStoredStep.run_work state.determinant state.adjugate
    (GeneralPaperBasisDirection.columnRun state.rows (next hj)).1 (rowPrefix new (Nat.le_of_lt hj))
    (new.coefficients.read (next hj))
  have h1 : j+1≤d+1 := by omega
  have h2 : j+d+2≤2*(d+1) := by omega
  have h3 : j+2≤d+1 := by omega
  have ha := Nat.mul_le_mul h1 h2
  have hb := Nat.pow_le_pow_left h3 2
  unfold componentWork
  nlinarith only [hp,hv,hu,ha,hb]

theorem all_work (d N : ℕ) (betaN : ℤ) (initialGrid : Vector d)
    (states : (i : Fin d) → State i.val d) (newRows : Fin d → Dense d) :
    (∑ i : Fin d,componentWork N betaN initialGrid (states i) i.isLt (newRows i))≤4096*d*(d+1)^2 := by
  calc
    _ ≤ ∑ _i : Fin d,4096*(d+1)^2 := Finset.sum_le_sum (fun i _ => stage_work N betaN initialGrid (states i) i.isLt (newRows i))
    _ = _ := by simp only [Finset.sum_const,Finset.card_fin,nsmul_eq_mul,Nat.cast_id]; ring

end Blotto.GeneralPaperBasisSolveLedger
