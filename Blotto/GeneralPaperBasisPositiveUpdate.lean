import Blotto.GeneralPaperBasisStoredCorrect

/-! A positive blocker directional coefficient supplies the new nonzero
determinant required by the exact stored update. The result is independent
of ray length, so an endpoint zero still increases the basis dimension.
-/
namespace Blotto.GeneralPaperBasisPositiveUpdate
open GeneralPaperBasisBorder GeneralPaperBasisIntegerCasts GeneralPaperBasisAdjugateBlock
open GeneralPaperBasisStoredProducts GeneralPaperBasisStoredCorrect GeneralPaperBasisStoredStep
set_option autoImplicit false
set_option maxHeartbeats 3000000

theorem next_nonzero {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (u v : Vector n) (a : ℤ)
    (x : Fin n → ℝ) (hSystem : (realMatrix M).mulVec x=realVector u.read) (hDet : M.det≠0)
    (hPositive : 0<((border (realMatrix M) (realVector u.read) (realVector v.read) (a:ℝ)).mulVec (direction x)) none) :
    determinantUpdate M.det M.adjugate u.read v.read a≠0 := by
  have hd : (realMatrix M).det≠0 := by rw [←det_cast]; exact_mod_cast hDet
  have hr := rank_increase (realMatrix M) (realVector u.read) (realVector v.read) (a:ℝ) x hSystem hd hPositive
  rw [←border_cast,←det_cast,integer_determinant M u.read v.read a hDet] at hr
  exact_mod_cast hr

theorem stored_from_positive {n : ℕ} (D : ℤ) (A : IntMatrix n) (M : Matrix (Fin n) (Fin n) ℤ)
    (u v : Vector n) (a : ℤ) (hValid : Valid D A M) (hDet : M.det≠0)
    (x : Fin n → ℝ) (hSystem : (realMatrix M).mulVec x=realVector u.read)
    (hPositive : 0<((border (realMatrix M) (realVector u.read) (realVector v.read) (a:ℝ)).mulVec (direction x)) none) :
    (run D A u v a).determinant≠0 ∧ Valid (run D A u v a).determinant (run D A u v a).adjugate (extended M u v a) :=
  run_correct D A M u v a hValid hDet (next_nonzero M u v a x hSystem hDet hPositive)

end Blotto.GeneralPaperBasisPositiveUpdate
