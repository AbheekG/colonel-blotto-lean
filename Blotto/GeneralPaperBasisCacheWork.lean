import Blotto.GeneralPaperBasisProductsWork

/-! The cached Schur/adjugate update with unit-price index operations in
both products and BOTH levels of the new matrix constructor. Every entry
uses the retained products; no minor/determinant/inverse is recomputed.
-/
namespace Blotto.GeneralPaperBasisCacheWork
open GeneralPaperBasisStoredProducts
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 4096

def rowRun {n : ℕ} (D Dnext : ℤ) (A : IntMatrix n) (au va : Vector n) (j : Fin (n+1)) : Vector (n+1) × ℕ :=
  PaperIndexedArrayConstruction.run (fun _ => 1) 1 (fun k => (GeneralPaperBasisStoredUpdate.entry D Dnext A au va j k,32))

theorem row_data {n : ℕ} (D Dnext : ℤ) (A : IntMatrix n) (au va : Vector n) (j : Fin (n+1)) :
    (rowRun D Dnext A au va j).1=(GeneralPaperBasisStoredUpdate.rowRun D Dnext A au va j).1 := by
  simp only [rowRun,GeneralPaperBasisStoredUpdate.rowRun,PaperIndexedArrayConstruction.run_data]

theorem row_work {n : ℕ} (D Dnext : ℤ) (A : IntMatrix n) (au va : Vector n) (j : Fin (n+1)) :
    (rowRun D Dnext A au va j).2≤256*(n+2) := by
  have hh := GeneralPaperUnitArrayReprice.work 1 (fun k : Fin (n+1) => (GeneralPaperBasisStoredUpdate.entry D Dnext A au va j k,32))
  change (rowRun D Dnext A au va j).2=(GeneralPaperBasisStoredUpdate.rowRun D Dnext A au va j).2+8*(n+1)+2 at hh
  have ho := GeneralPaperBasisStoredUpdate.row_work D Dnext A au va j
  omega

def matrixRun {n : ℕ} (D Dnext : ℤ) (A : IntMatrix n) (au va : Vector n) : IntMatrix (n+1) × ℕ :=
  PaperIndexedArrayConstruction.run (fun _ => 1) 1 (rowRun D Dnext A au va)

theorem matrix_data {n : ℕ} (D Dnext : ℤ) (A : IntMatrix n) (au va : Vector n) :
    (matrixRun D Dnext A au va).1=(GeneralPaperBasisStoredUpdate.matrixRun D Dnext A au va).1 := by
  simp only [matrixRun,GeneralPaperBasisStoredUpdate.matrixRun,PaperIndexedArrayConstruction.run_data,row_data]

theorem matrix_work {n : ℕ} (D Dnext : ℤ) (A : IntMatrix n) (au va : Vector n) :
    (matrixRun D Dnext A au va).2≤512*(n+2)^2 := by
  have hs := Finset.sum_le_sum (fun j (_ : j∈Finset.univ) => row_work D Dnext A au va j)
  simp only [Finset.sum_const,Finset.card_fin,nsmul_eq_mul,Nat.cast_id] at hs
  have hh := PaperIndexedArrayConstruction.run_work (fun _ => 1) 1 (rowRun D Dnext A au va)
  have ho := GeneralPaperUnitArrayOverhead.overhead 1 (n+1) (n+1)
  change (matrixRun D Dnext A au va).2=_ at hh
  nlinarith only [hh,hs,ho]

def run {n : ℕ} (D : ℤ) (A : IntMatrix n) (u v : Vector n) (a : ℤ) : GeneralPaperBasisStoredStep.Result n :=
  let au := GeneralPaperBasisProductsWork.mulVecRun A u
  let va := GeneralPaperBasisProductsWork.rowRun v A
  let dot := GeneralPaperBasisIntegerDot.run v.read au.1.read
  let Dnext := a*D-dot.value
  let matrix := matrixRun D Dnext A au.1 va.1
  ⟨Dnext,matrix.1,au.2+va.2+dot.work+matrix.2+24⟩

theorem determinant_data {n : ℕ} (D : ℤ) (A : IntMatrix n) (u v : Vector n) (a : ℤ) :
    (run D A u v a).determinant=(GeneralPaperBasisStoredStep.run D A u v a).determinant := by
  simp only [run,GeneralPaperBasisStoredStep.run,GeneralPaperBasisProductsWork.mulVec_data]

theorem adjugate_data {n : ℕ} (D : ℤ) (A : IntMatrix n) (u v : Vector n) (a : ℤ) :
    (run D A u v a).adjugate=(GeneralPaperBasisStoredStep.run D A u v a).adjugate := by
  simp only [run,GeneralPaperBasisStoredStep.run,GeneralPaperBasisProductsWork.mulVec_data,
    GeneralPaperBasisProductsWork.row_data,matrix_data]

theorem work {n : ℕ} (D : ℤ) (A : IntMatrix n) (u v : Vector n) (a : ℤ) :
    (run D A u v a).work≤2048*(n+2)^2 := by
  have hu := GeneralPaperBasisProductsWork.mulVec_work A u
  have hv := GeneralPaperBasisProductsWork.row_work v A
  have hd := GeneralPaperBasisIntegerDot.run_work v.read (GeneralPaperBasisProductsWork.mulVecRun A u).1.read
  have hm := matrix_work D (run D A u v a).determinant A (GeneralPaperBasisProductsWork.mulVecRun A u).1 (GeneralPaperBasisProductsWork.rowRun v A).1
  change _+_+_+(matrixRun D (run D A u v a).determinant A (GeneralPaperBasisProductsWork.mulVecRun A u).1 (GeneralPaperBasisProductsWork.rowRun v A).1).2+24≤_
  nlinarith only [hu,hv,hd,hm]

end Blotto.GeneralPaperBasisCacheWork
