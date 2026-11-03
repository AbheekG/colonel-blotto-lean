import Blotto.GeneralPaperBasisAdjugateSolve

/-! An exact scaled inverse is the adjugate. This proof uses only the
retained adjugate multiplication identities and a nonzero determinant;
it does not compute or assume a matrix inverse.
-/
namespace Blotto.GeneralPaperBasisAdjugateUnique
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem adjugate_unique {i : Type*} [Fintype i] [DecidableEq i] (M B : Matrix i i ℝ)
    (hDet : M.det≠0) (hProduct : M*B=M.det • (1 : Matrix i i ℝ)) : B=M.adjugate := by
  have hh := congrArg (fun C : Matrix i i ℝ => M.adjugate*C) hProduct
  rw [←Matrix.mul_assoc,Matrix.adjugate_mul] at hh
  simp only [Matrix.smul_mul,Matrix.one_mul,Matrix.mul_smul,Matrix.mul_one] at hh
  ext j k
  have he := congrFun (congrFun hh j) k
  change M.det*B j k=M.det*M.adjugate j k at he
  exact mul_left_cancel₀ hDet he

theorem sum_quotient {i : Type*} [Fintype i] (w p q : i → ℝ) (s c D : ℝ) :
    (∑ j,w j*((s*p j+q j*c)/D))=(s*(∑ j,w j*p j)+(∑ j,w j*q j)*c)/D := by
  calc
    _ = ∑ j,(s*(w j*p j)+(w j*q j)*c)/D := by apply Finset.sum_congr rfl; intro j _; ring
    _ = _ := by rw [←Finset.sum_div]; simp only [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.sum_mul]

end Blotto.GeneralPaperBasisAdjugateUnique
