import Blotto.GeneralPaperBasisStoredUpdate

/-! Executed integer determinant/adjugate step. Au, vA and vAu are
evaluated once and cached; the new determinant and matrix are returned.
No determinant, adjugate or inverse routine occurs in the executed body.
-/
namespace Blotto.GeneralPaperBasisStoredStep
open GeneralPaperBasisStoredProducts GeneralPaperBasisAdjugateBlock
set_option autoImplicit false
set_option maxHeartbeats 3000000

structure Result (n : ℕ) where
  determinant : ℤ
  adjugate : IntMatrix (n+1)
  work : ℕ

def run {n : ℕ} (D : ℤ) (A : IntMatrix n) (u v : Vector n) (a : ℤ) : Result n :=
  let au := mulVecRun A u
  let va := rowRun v A
  let dot := GeneralPaperBasisIntegerDot.run v.read au.1.read
  let Dnext := a*D-dot.value
  let newMatrix := GeneralPaperBasisStoredUpdate.matrixRun D Dnext A au.1 va.1
  ⟨Dnext,newMatrix.1,au.2+va.2+dot.work+newMatrix.2+24⟩

theorem determinant_data {n : ℕ} (D : ℤ) (A : IntMatrix n) (u v : Vector n) (a : ℤ) :
    (run D A u v a).determinant=determinantUpdate D (observe A) u.read v.read a := by
  change a*D-(GeneralPaperBasisIntegerDot.run v.read (mulVecRun A u).1.read).value=_
  rw [GeneralPaperBasisIntegerDot.run_value,mulVec_data]
  rfl

theorem adjugate_data {n : ℕ} (D : ℤ) (A : IntMatrix n) (u v : Vector n) (a : ℤ) :
    observe (run D A u v a).adjugate=
      (GeneralPaperBasisIntegerUpdate.update D (run D A u v a).determinant (observe A)
        ((observe A).mulVec u.read) (rowProduct v.read (observe A))).submatrix
          (GeneralPaperBasisAppendIndex.decode n) (GeneralPaperBasisAppendIndex.decode n) := by
  change observe (GeneralPaperBasisStoredUpdate.matrixRun D (run D A u v a).determinant A
    (mulVecRun A u).1 (rowRun v A).1).1=_
  rw [GeneralPaperBasisStoredUpdate.matrix_data,mulVec_data,row_data]

theorem run_work {n : ℕ} (D : ℤ) (A : IntMatrix n) (u v : Vector n) (a : ℤ) :
    (run D A u v a).work≤1024*(n+2)^2 := by
  have hAU := mulVec_work A u
  have hVA := row_work v A
  have hDot := GeneralPaperBasisIntegerDot.run_work v.read (mulVecRun A u).1.read
  have hNew := GeneralPaperBasisStoredUpdate.matrix_work D (run D A u v a).determinant A (mulVecRun A u).1 (rowRun v A).1
  change (mulVecRun A u).2+(rowRun v A).2+(GeneralPaperBasisIntegerDot.run v.read (mulVecRun A u).1.read).work+
    (GeneralPaperBasisStoredUpdate.matrixRun D (run D A u v a).determinant A (mulVecRun A u).1 (rowRun v A).1).2+24≤_
  nlinarith only [hAU,hVA,hDot,hNew]

end Blotto.GeneralPaperBasisStoredStep
