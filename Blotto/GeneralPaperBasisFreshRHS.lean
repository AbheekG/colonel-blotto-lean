import Blotto.GeneralPaperBasisPrefixSum

/-! Fresh N-scaled right-hand sides from the ORIGINAL retained dense
rows and the FIXED initial grid numerators. Later coordinates are never
copied from an intermediate ray-test point, so their denominators do not
accumulate across stages.
-/
namespace Blotto.GeneralPaperBasisFreshRHS
open GeneralPaperBasisStoredProducts GeneralPaperBasisDenseRow GeneralPaperBasisPrefixSum
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 3000000

abbrev Rows (j d : ℕ) := FixedArrayTable j (Dense d)

def minor {j d : ℕ} (rows : Rows j d) (hj : j≤d) : Matrix (Fin j) (Fin j) ℤ :=
  fun i k => (rows.read i).coefficients.read (embed hj k)

def column {j d : ℕ} (rows : Rows j d) (next : Fin d) : Vector j :=
  FixedArrayTable.ofFn (fun i => (rows.read i).coefficients.read next)

def tailVector {d : ℕ} (j : ℕ) (initial : Vector d) : Fin d → ℤ :=
  fun k => if j≤k.val then initial.read k else 0

def rhsRun {j d : ℕ} (N : ℕ) (betaN : ℤ) (rows : Rows j d) (initial : Vector d) : Vector j × ℕ :=
  PaperIndexedArrayConstruction.run (fun _ => 0) 1 (fun i =>
    let row := rows.read i
    let tail := GeneralPaperBasisIntegerDot.run row.coefficients.read (tailVector j initial)
    ((N:ℤ)*row.constant+betaN*row.slope-tail.value,tail.work+12))

theorem rhs_data {j d : ℕ} (N : ℕ) (betaN : ℤ) (rows : Rows j d) (initial : Vector d) (i : Fin j) :
    (rhsRun N betaN rows initial).1.read i=(N:ℤ)*(rows.read i).constant+betaN*(rows.read i).slope-
      ∑ k : Fin d,if j≤k.val then (rows.read i).coefficients.read k*initial.read k else 0 := by
  simp only [rhsRun,PaperIndexedArrayConstruction.run_data,FixedArrayTable.read_ofFn,GeneralPaperBasisIntegerDot.run_value,
    tailVector,mul_ite,mul_zero]

theorem rhs_work {j d : ℕ} (N : ℕ) (betaN : ℤ) (rows : Rows j d) (initial : Vector d) :
    (rhsRun N betaN rows initial).2≤128*(j+1)*(d+1) := by
  have hh := PaperIndexedArrayConstruction.run_work_bound (fun _ => 0) 0 (fun _ => by simp) 1
    (fun i => ((N:ℤ)*(rows.read i).constant+betaN*(rows.read i).slope-
      (GeneralPaperBasisIntegerDot.run (rows.read i).coefficients.read (tailVector j initial)).value,
        (GeneralPaperBasisIntegerDot.run (rows.read i).coefficients.read (tailVector j initial)).work+12))
  change (rhsRun N betaN rows initial).2≤(∑ i : Fin j,
    ((GeneralPaperBasisIntegerDot.run (rows.read i).coefficients.read (tailVector j initial)).work+12))+
      (j+1)*(6+10*0*binaryWordWidth (j+1)+28) at hh
  have hs : (∑ i : Fin j,((GeneralPaperBasisIntegerDot.run (rows.read i).coefficients.read (tailVector j initial)).work+12))=j*(16*d+6+12) := by
    simp only [GeneralPaperBasisIntegerDot.run_work,Finset.sum_const,Finset.card_fin,nsmul_eq_mul,Nat.cast_id]
  rw [hs] at hh
  norm_num only [Nat.mul_zero,Nat.zero_mul,Nat.add_zero,Nat.reduceAdd] at hh
  nlinarith only [hh]

end Blotto.GeneralPaperBasisFreshRHS
