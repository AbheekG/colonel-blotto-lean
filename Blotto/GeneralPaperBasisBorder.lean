import Blotto.GeneralPaperRayEndpointReal

/-! An original-basis extension, with the appended row/column indexed by
none and old rows/columns by some. Simultaneous reindexing later places
the appended coordinate last without changing its determinant.
-/
namespace Blotto.GeneralPaperBasisBorder
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2500000

def border {i R : Type*} (M : Matrix i i R) (u v : i → R) (a : R) : Matrix (Option i) (Option i) R
  | none,none => a
  | some j,none => u j
  | none,some k => v k
  | some j,some k => M j k

theorem submatrix_old {i R : Type*} (M : Matrix i i R) (u v : i → R) (a : R) :
    (border M u v a).submatrix some some=M := rfl

theorem real_determinant {i : Type*} [Fintype i] [DecidableEq i]
    (M : Matrix i i ℝ) (u v : i → ℝ) (a : ℝ) (x : i → ℝ) (hSystem : M.mulVec x=u) :
    (border M u v a).det=M.det*(a-∑ j,v j*x j) := by
  apply GeneralPaperBorderedDeterminant.determinant_of_solution (border M u v a) x
  intro j
  exact (congrFun hSystem j).symm

def direction {i : Type*} (x : i → ℝ) : Option i → ℝ
  | none => 1
  | some j => -x j

theorem direction_old {i : Type*} [Fintype i] [DecidableEq i]
    (M : Matrix i i ℝ) (u v : i → ℝ) (a : ℝ) (x : i → ℝ) (j : i) :
    ((border M u v a).mulVec (direction x)) (some j)=u j-(M.mulVec x) j := by
  simp only [Matrix.mulVec,dotProduct,Fintype.sum_option,border,direction,mul_one,mul_neg,Finset.sum_neg_distrib]
  ring

theorem direction_new {i : Type*} [Fintype i] [DecidableEq i]
    (M : Matrix i i ℝ) (u v : i → ℝ) (a : ℝ) (x : i → ℝ) :
    ((border M u v a).mulVec (direction x)) none=a-∑ j,v j*x j := by
  simp only [Matrix.mulVec,dotProduct,Fintype.sum_option,border,direction,mul_one,mul_neg,Finset.sum_neg_distrib]
  ring

theorem rank_increase {i : Type*} [Fintype i] [DecidableEq i]
    (M : Matrix i i ℝ) (u v : i → ℝ) (a : ℝ) (x : i → ℝ) (hSystem : M.mulVec x=u)
    (hDet : M.det≠0) (hPositive : 0<((border M u v a).mulVec (direction x)) none) :
    (border M u v a).det≠0 := by
  rw [real_determinant M u v a x hSystem]
  apply mul_ne_zero hDet
  rw [direction_new] at hPositive
  exact hPositive.ne'

end Blotto.GeneralPaperBasisBorder
