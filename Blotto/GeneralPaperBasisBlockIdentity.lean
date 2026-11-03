import Blotto.GeneralPaperBasisAdjugateBlock

/-! The computed bordered determinant equals the actual new determinant.
For a nonsingular extension, the scaled-product certificate identifies
the displayed block update with the actual new adjugate.
-/
namespace Blotto.GeneralPaperBasisBlockIdentity
open GeneralPaperBasisBorder GeneralPaperBasisAdjugateSolve GeneralPaperBasisAdjugateBlock
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 3500000

theorem determinant_formula {i : Type*} [Fintype i] [DecidableEq i] (M : Matrix i i ℝ)
    (u v : i → ℝ) (a : ℝ) (hDet : M.det≠0) :
    (border M u v a).det=determinantUpdate M.det M.adjugate u v a := by
  rw [real_determinant M u v a (solve M.adjugate M.det u) (solve_system M u hDet)]
  have hs : (∑ j,v j*(solve M.adjugate M.det u j))=(∑ j,v j*(M.adjugate.mulVec u j))/M.det := by
    simp only [solve,←mul_div_assoc,←Finset.sum_div]
  rw [hs]
  unfold determinantUpdate
  field_simp

theorem adjugate_formula {i : Type*} [Fintype i] [DecidableEq i] (M : Matrix i i ℝ)
    (u v : i → ℝ) (a : ℝ) (hDet : M.det≠0)
    (hNext : determinantUpdate M.det M.adjugate u v a≠0) :
    candidate M.det (determinantUpdate M.det M.adjugate u v a) M.adjugate
      (M.adjugate.mulVec u) (rowProduct v M.adjugate)=(border M u v a).adjugate := by
  have hd := determinant_formula M u v a hDet
  apply GeneralPaperBasisAdjugateUnique.adjugate_unique (border M u v a) _ (by rwa [hd])
  calc
    _ = determinantUpdate M.det M.adjugate u v a • (1 : Matrix (Option i) (Option i) ℝ) := scaled_product M u v a hDet
    _ = _ := by rw [hd]

end Blotto.GeneralPaperBasisBlockIdentity
