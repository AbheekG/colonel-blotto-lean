import Blotto.GeneralPaperTransferCofactorBounds

/-! Bordered determinant identity from an actual solution of the defining
equations. One RHS-column elimination and a triangular block determinant
suffice; no new Schur-complement dependency or inverse oracle is needed.
-/
namespace Blotto.GeneralPaperBorderedDeterminant
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem determinant_of_solution {v : Type*} [Fintype v] [DecidableEq v]
    (F : Matrix (Option v) (Option v) ℝ) (x : v → ℝ)
    (hSystem : ∀ i, F (some i) none=∑ j,F (some i) (some j)*x j) :
    F.det=(F.submatrix some some).det*(F none none-∑ j,F none (some j)*x j) := by
  let c : Option v → ℝ := fun j => match j with | none => 1 | some j => -x j
  let N := F.updateCol none (fun i => ∑ j,c j*F i j)
  have hDet : N.det=F.det := by
    have he := Matrix.det_updateCol_sum F none c
    simpa only [N,c,smul_eq_mul,one_mul] using he
  have hColumn (i : Option v) : N i none=F i none-∑ j,F i (some j)*x j := by
    change (∑ j,c j*F i j)=_
    rw [Fintype.sum_option]
    simp only [c,one_mul,neg_mul,Finset.sum_neg_distrib]
    congr 1
    exact congrArg (fun value : ℝ => -value) (Finset.sum_congr rfl (fun j _ => mul_comm _ _))
  have hOther (i : Option v) (j : v) : N i (some j)=F i (some j) := by
    exact Matrix.updateCol_ne (show some j≠none by simp)
  let e : Option v ≃ v ⊕ PUnit.{1} := Equiv.optionEquivSumPUnit v
  let A := F.submatrix some some
  let C : Matrix PUnit.{1} v ℝ := fun _ j => F none (some j)
  let D : Matrix PUnit.{1} PUnit.{1} ℝ := fun _ _ => F none none-∑ j,F none (some j)*x j
  have hBlock : N.submatrix e.symm e.symm=Matrix.fromBlocks A 0 C D := by
    ext i j
    cases i with
    | inl i =>
      cases j with
      | inl j =>
        change N (some i) (some j)=F (some i) (some j)
        exact hOther _ _
      | inr j =>
        change N (some i) none=0
        rw [hColumn,hSystem,sub_self]
    | inr i =>
      cases j with
      | inl j =>
        change N none (some j)=F none (some j)
        exact hOther _ _
      | inr j =>
        change N none none=F none none-∑ j,F none (some j)*x j
        exact hColumn none
  calc
    F.det = N.det := hDet.symm
    _ = (N.submatrix e.symm e.symm).det := (Matrix.det_submatrix_equiv_self e.symm N).symm
    _ = A.det*D.det := by rw [hBlock,Matrix.det_fromBlocks_zero₁₂]
    _ = _ := by rw [Matrix.det_unique D]

end Blotto.GeneralPaperBorderedDeterminant
