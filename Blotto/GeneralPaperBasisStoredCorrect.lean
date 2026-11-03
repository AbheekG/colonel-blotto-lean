import Blotto.GeneralPaperBasisStoredStep

/-! The stored step preserves the determinant/adjugate cache invariant for
the actual appended matrix, with the new row and column in the last slot.
The initial empty basis has determinant one and an empty stored adjugate.
-/
namespace Blotto.GeneralPaperBasisStoredCorrect
open GeneralPaperBasisStoredProducts GeneralPaperBasisStoredStep GeneralPaperBasisBorder GeneralPaperBasisAdjugateBlock
set_option autoImplicit false
set_option maxHeartbeats 3000000

def Valid {n : ℕ} (D : ℤ) (A : IntMatrix n) (M : Matrix (Fin n) (Fin n) ℤ) : Prop := D=M.det ∧ observe A=M.adjugate

def extended {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (u v : Vector n) (a : ℤ) : Matrix (Fin (n+1)) (Fin (n+1)) ℤ :=
  (border M u.read v.read a).submatrix (GeneralPaperBasisAppendIndex.decode n) (GeneralPaperBasisAppendIndex.decode n)

theorem run_correct {n : ℕ} (D : ℤ) (A : IntMatrix n) (M : Matrix (Fin n) (Fin n) ℤ)
    (u v : Vector n) (a : ℤ) (hValid : Valid D A M) (hDet : M.det≠0)
    (hNext : determinantUpdate M.det M.adjugate u.read v.read a≠0) :
    (run D A u v a).determinant≠0 ∧ Valid (run D A u v a).determinant (run D A u v a).adjugate (extended M u v a) := by
  have hd : (run D A u v a).determinant=determinantUpdate M.det M.adjugate u.read v.read a := by
    rw [determinant_data,hValid.1,hValid.2]
  have hNewD : (run D A u v a).determinant=(extended M u v a).det := by
    rw [extended,GeneralPaperBasisAppendIndex.determinant_reindex,GeneralPaperBasisIntegerCasts.integer_determinant M u.read v.read a hDet]
    exact hd
  have hA : observe (run D A u v a).adjugate=
      (border M u.read v.read a).adjugate.submatrix
        (GeneralPaperBasisAppendIndex.decode n) (GeneralPaperBasisAppendIndex.decode n) := by
    rw [adjugate_data,hd,hValid.1,hValid.2,GeneralPaperBasisIntegerUpdate.update_correct M u.read v.read a hDet hNext]
  refine ⟨by rwa [hd],hNewD,?_⟩
  change observe (run D A u v a).adjugate=
    ((border M u.read v.read a).submatrix (GeneralPaperBasisAppendIndex.decode n) (GeneralPaperBasisAppendIndex.decode n)).adjugate
  rw [GeneralPaperBasisAppendIndex.adjugate_reindex]
  exact hA

def initial : ℤ × IntMatrix 0 := (1,FixedArrayTable.ofFn (fun j => Fin.elim0 j))

theorem initial_valid (M : Matrix (Fin 0) (Fin 0) ℤ) : Valid initial.1 initial.2 M := by
  refine ⟨?_,?_⟩
  · simp [initial]
  · funext j
    exact Fin.elim0 j

end Blotto.GeneralPaperBasisStoredCorrect
