import Blotto.GeneralPaperBasisBorder

/-! Solving with a retained adjugate uses one matrix-vector product and
one common determinant. This is the algebra for fresh point/direction
solves; the executed integer arrays and denominator ledger follow it.
-/
namespace Blotto.GeneralPaperBasisAdjugateSolve
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2500000

noncomputable def solve {i : Type*} [Fintype i] (A : Matrix i i ℝ) (D : ℝ) (b : i → ℝ) : i → ℝ :=
  fun j => (A.mulVec b j)/D

theorem solve_system {i : Type*} [Fintype i] [DecidableEq i] (M : Matrix i i ℝ) (b : i → ℝ) (hDet : M.det≠0) :
    M.mulVec (solve M.adjugate M.det b)=b := by
  have hm := congrArg (fun A : Matrix i i ℝ => A.mulVec b) (Matrix.mul_adjugate M)
  rw [←Matrix.mulVec_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec] at hm
  funext j
  have hj := congrFun hm j
  change (∑ k,M j k*((M.adjugate.mulVec b k)/M.det))=b j
  simp only [←mul_div_assoc,←Finset.sum_div]
  change (M.mulVec (M.adjugate.mulVec b) j)/M.det=b j
  rw [hj]
  change (M.det*b j)/M.det=b j
  exact mul_div_cancel_left₀ _ hDet

theorem scaled_solution {i : Type*} [Fintype i] [DecidableEq i] (M : Matrix i i ℝ) (b x : i → ℝ)
    (hSystem : M.mulVec x=b) : M.adjugate.mulVec b=M.det • x := by
  rw [←hSystem,Matrix.mulVec_mulVec,Matrix.adjugate_mul,Matrix.smul_mulVec,Matrix.one_mulVec]

theorem unique_solution {i : Type*} [Fintype i] [DecidableEq i] (M : Matrix i i ℝ) (b x : i → ℝ)
    (hDet : M.det≠0) (hSystem : M.mulVec x=b) : x=solve M.adjugate M.det b := by
  have hh := scaled_solution M b x hSystem
  funext j
  have hj := congrFun hh j
  change x j=(M.adjugate.mulVec b j)/M.det
  rw [hj]
  exact (mul_div_cancel_left₀ _ hDet).symm

end Blotto.GeneralPaperBasisAdjugateSolve
