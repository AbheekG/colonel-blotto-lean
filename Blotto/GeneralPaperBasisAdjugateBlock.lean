import Blotto.GeneralPaperBasisAdjugateUnique

/-! The paper's bordered determinant and adjugate formula. Only two
matrix-vector products and an outer product occur in the update. Real
matrices here are erased correctness observers of the integer update.
-/
namespace Blotto.GeneralPaperBasisAdjugateBlock
open GeneralPaperBasisBorder GeneralPaperBasisAdjugateUnique
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 3500000

def rowProduct {i R : Type*} [Fintype i] [CommSemiring R] (v : i → R) (A : Matrix i i R) : i → R :=
  fun j => ∑ k,v k*A k j

def determinantUpdate {i R : Type*} [Fintype i] [CommRing R]
    (D : R) (A : Matrix i i R) (u v : i → R) (a : R) : R := a*D-∑ j,v j*(A.mulVec u j)

noncomputable def candidate {i : Type*} (D Dnext : ℝ) (A : Matrix i i ℝ) (au va : i → ℝ) :
    Matrix (Option i) (Option i) ℝ :=
  border (fun j k => (Dnext*A j k+au j*va k)/D) (fun j => -au j) (fun k => -va k) D

theorem scaled_product {i : Type*} [Fintype i] [DecidableEq i] (M : Matrix i i ℝ)
    (u v : i → ℝ) (a : ℝ) (hDet : M.det≠0) :
    border M u v a * candidate M.det (determinantUpdate M.det M.adjugate u v a)
      M.adjugate (M.adjugate.mulVec u) (rowProduct v M.adjugate)=
        determinantUpdate M.det M.adjugate u v a • (1 : Matrix (Option i) (Option i) ℝ) := by
  let D := M.det
  let A := M.adjugate
  let au := A.mulVec u
  let va := rowProduct v A
  let Dnext := determinantUpdate D A u v a
  have hMU (j : i) : (∑ k,M j k*au k)=D*u j := by
    have hh := congrArg (fun C : Matrix i i ℝ => C.mulVec u) (Matrix.mul_adjugate M)
    rw [←Matrix.mulVec_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec] at hh
    exact congrFun hh j
  have hMA (j k : i) : (∑ l,M j l*A l k)=D*(if j=k then 1 else 0) := by
    exact congrFun (congrFun (Matrix.mul_adjugate M) j) k
  change border M u v a * candidate D Dnext A au va=Dnext • (1 : Matrix (Option i) (Option i) ℝ)
  ext p q
  cases p with
  | none =>
    cases q with
    | none =>
      rw [Matrix.mul_apply,Fintype.sum_option]
      simp only [candidate,border,Matrix.smul_apply,smul_eq_mul,Matrix.one_apply,ite_true,mul_one]
      change a*D+(∑ j,v j*(-au j))=Dnext
      simp only [mul_neg,Finset.sum_neg_distrib]
      rfl
    | some k =>
      rw [Matrix.mul_apply,Fintype.sum_option]
      simp only [candidate,border,Matrix.smul_apply,smul_eq_mul,Matrix.one_apply,reduceCtorEq,ite_false,mul_zero]
      change a*(-va k)+(∑ j,v j*((Dnext*A j k+au j*va k)/D))=0
      rw [sum_quotient]
      change a*(-va k)+(Dnext*va k+(∑ j,v j*au j)*va k)/D=0
      dsimp only [Dnext,determinantUpdate,au]
      field_simp [show D≠0 from hDet]
      ring
  | some j =>
    cases q with
    | none =>
      rw [Matrix.mul_apply,Fintype.sum_option]
      simp only [candidate,border,Matrix.smul_apply,smul_eq_mul,Matrix.one_apply,reduceCtorEq,ite_false,mul_zero]
      change u j*D+(∑ k,M j k*(-au k))=0
      simp only [mul_neg,Finset.sum_neg_distrib]
      rw [hMU]
      ring
    | some k =>
      rw [Matrix.mul_apply,Fintype.sum_option]
      simp only [candidate,border,Matrix.smul_apply,smul_eq_mul,Matrix.one_apply,Option.some.injEq]
      change u j*(-va k)+(∑ l,M j l*((Dnext*A l k+au l*va k)/D))=Dnext*(if j=k then 1 else 0)
      rw [sum_quotient,hMA,hMU]
      field_simp [show D≠0 from hDet]
      ring

end Blotto.GeneralPaperBasisAdjugateBlock
