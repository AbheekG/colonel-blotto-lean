import Blotto.GeneralPaperBasisStoredProducts

/-! Materialize the exact integer adjugate update in a new (j+1)-square
stored array. The two products Au and vA have already been stored once;
one scalar formula is evaluated per new entry, without recursive calls.
-/
namespace Blotto.GeneralPaperBasisStoredUpdate
open GeneralPaperBasisStoredProducts
set_option autoImplicit false
set_option maxHeartbeats 3000000

def entry {n : ℕ} (D Dnext : ℤ) (A : IntMatrix n) (au va : Vector n) (j k : Fin (n+1)) : ℤ :=
  match GeneralPaperBasisAppendIndex.decode n j,GeneralPaperBasisAppendIndex.decode n k with
  | none,none => D
  | some i,none => -(au.read i)
  | none,some l => -(va.read l)
  | some i,some l => (Dnext*(A.read i).read l+au.read i*va.read l)/D

def rowRun {n : ℕ} (D Dnext : ℤ) (A : IntMatrix n) (au va : Vector n) (j : Fin (n+1)) : Vector (n+1) × ℕ :=
  PaperIndexedArrayConstruction.run (fun _ => 0) 1 (fun k => (entry D Dnext A au va j k,32))

def matrixRun {n : ℕ} (D Dnext : ℤ) (A : IntMatrix n) (au va : Vector n) : IntMatrix (n+1) × ℕ :=
  PaperIndexedArrayConstruction.run (fun _ => 0) 1 (rowRun D Dnext A au va)

theorem matrix_data {n : ℕ} (D Dnext : ℤ) (A : IntMatrix n) (au va : Vector n) :
    observe (matrixRun D Dnext A au va).1=
      (GeneralPaperBasisIntegerUpdate.update D Dnext (observe A) au.read va.read).submatrix
        (GeneralPaperBasisAppendIndex.decode n) (GeneralPaperBasisAppendIndex.decode n) := by
  funext j k
  simp only [observe,matrixRun,rowRun,PaperIndexedArrayConstruction.run_data,FixedArrayTable.read_ofFn]
  cases hj : GeneralPaperBasisAppendIndex.decode n j <;> cases hk : GeneralPaperBasisAppendIndex.decode n k <;>
    simp only [entry,hj,hk,GeneralPaperBasisIntegerUpdate.update,GeneralPaperBasisBorder.border,Matrix.submatrix_apply]
  all_goals rfl

theorem row_work {n : ℕ} (D Dnext : ℤ) (A : IntMatrix n) (au va : Vector n) (j : Fin (n+1)) :
    (rowRun D Dnext A au va j).2≤128*(n+2) := by
  have hh := PaperIndexedArrayConstruction.run_work_bound (fun _ => 0) 0 (fun _ => by simp) 1
    (fun k => (entry D Dnext A au va j k,32))
  simp only [Finset.sum_const,Finset.card_fin,nsmul_eq_mul,Nat.cast_id,Nat.mul_zero,Nat.zero_mul,Nat.add_zero] at hh
  change (rowRun D Dnext A au va j).2≤_ at hh
  omega

theorem matrix_work {n : ℕ} (D Dnext : ℤ) (A : IntMatrix n) (au va : Vector n) :
    (matrixRun D Dnext A au va).2≤256*(n+2)^2 := by
  have hs := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => row_work D Dnext A au va j)
  simp only [Finset.sum_const,Finset.card_fin,nsmul_eq_mul,Nat.cast_id] at hs
  have hh := PaperIndexedArrayConstruction.run_work_bound (fun _ => 0) 0 (fun _ => by simp) 1 (rowRun D Dnext A au va)
  simp only [Nat.mul_zero,Nat.zero_mul,Nat.add_zero] at hh
  change (matrixRun D Dnext A au va).2≤_ at hh
  nlinarith only [hs,hh]

end Blotto.GeneralPaperBasisStoredUpdate
