import Blotto.GeneralPaperBasisBlockIdentity

/-! Integer observers for exact basis updates. Cast identities connect
literal integer sums/products and the original integer determinants to
the real adjugate/Schur proofs without a coefficient or inverse oracle.
-/
namespace Blotto.GeneralPaperBasisIntegerCasts
open GeneralPaperBasisBorder GeneralPaperBasisAdjugateBlock
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 3000000

noncomputable def realMatrix {i j : Type*} (M : Matrix i j ℤ) : Matrix i j ℝ := fun a b => (M a b:ℝ)
noncomputable def realVector {i : Type*} (v : i → ℤ) : i → ℝ := fun a => (v a:ℝ)

theorem det_cast {i : Type*} [Fintype i] [DecidableEq i] (M : Matrix i i ℤ) : (M.det:ℝ)=(realMatrix M).det :=
  (Int.castRingHom ℝ).map_det M

theorem adjugate_cast {i : Type*} [Fintype i] [DecidableEq i] (M : Matrix i i ℤ) :
    realMatrix M.adjugate=(realMatrix M).adjugate := (Int.castRingHom ℝ).map_adjugate M

theorem mulVec_cast {i : Type*} [Fintype i] (M : Matrix i i ℤ) (u : i → ℤ) :
    realVector (M.mulVec u)=(realMatrix M).mulVec (realVector u) := by
  funext j
  simp only [realVector,realMatrix,Matrix.mulVec,dotProduct,Int.cast_sum,Int.cast_mul]

theorem rowProduct_cast {i : Type*} [Fintype i] (v : i → ℤ) (M : Matrix i i ℤ) :
    realVector (rowProduct v M)=rowProduct (realVector v) (realMatrix M) := by
  funext j
  simp only [realVector,realMatrix,rowProduct,Int.cast_sum,Int.cast_mul]

theorem border_cast {i : Type*} (M : Matrix i i ℤ) (u v : i → ℤ) (a : ℤ) :
    realMatrix (border M u v a)=border (realMatrix M) (realVector u) (realVector v) (a:ℝ) := by
  ext j k
  cases j <;> cases k <;> rfl

theorem update_cast {i : Type*} [Fintype i] (D : ℤ) (A : Matrix i i ℤ) (u v : i → ℤ) (a : ℤ) :
    ((determinantUpdate D A u v a:ℤ):ℝ)=
      determinantUpdate (D:ℝ) (realMatrix A) (realVector u) (realVector v) (a:ℝ) := by
  simp only [determinantUpdate,realMatrix,realVector,Matrix.mulVec,dotProduct,Int.cast_sub,Int.cast_mul,Int.cast_sum]

theorem integer_determinant {i : Type*} [Fintype i] [DecidableEq i] (M : Matrix i i ℤ)
    (u v : i → ℤ) (a : ℤ) (hDet : M.det≠0) :
    (border M u v a).det=determinantUpdate M.det M.adjugate u v a := by
  have hd : (realMatrix M).det≠0 := by rw [←det_cast]; exact_mod_cast hDet
  have hr := GeneralPaperBasisBlockIdentity.determinant_formula (realMatrix M) (realVector u) (realVector v) (a:ℝ) hd
  rw [←det_cast M,←adjugate_cast M,←update_cast,←border_cast,←det_cast] at hr
  exact_mod_cast hr

end Blotto.GeneralPaperBasisIntegerCasts
