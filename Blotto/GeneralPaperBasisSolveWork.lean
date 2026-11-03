import Blotto.GeneralPaperBasisCacheWork

/-! Fresh original RHS and rational prefix solves with unit index prices.
The retained adjugate is read once per dot term; fresh RHS data and the
fixed common denominator are exactly the native ones.
-/
namespace Blotto.GeneralPaperBasisSolveWork
open GeneralPaperBasisStoredProducts GeneralPaperBasisFreshRHS
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 4096

def rhsRun {j d : ℕ} (N : ℕ) (betaN : ℤ) (rows : Rows j d) (initial : Vector d) : Vector j × ℕ :=
  PaperIndexedArrayConstruction.run (fun _ => 1) 1 (fun i =>
    let row := rows.read i
    let tail := GeneralPaperBasisIntegerDot.run row.coefficients.read (tailVector j initial)
    ((N:ℤ)*row.constant+betaN*row.slope-tail.value,tail.work+12))

theorem rhs_data {j d : ℕ} (N : ℕ) (betaN : ℤ) (rows : Rows j d) (initial : Vector d) :
    (rhsRun N betaN rows initial).1=(GeneralPaperBasisFreshRHS.rhsRun N betaN rows initial).1 := by
  simp only [rhsRun,GeneralPaperBasisFreshRHS.rhsRun,PaperIndexedArrayConstruction.run_data]

theorem rhs_work {j d : ℕ} (N : ℕ) (betaN : ℤ) (rows : Rows j d) (initial : Vector d) :
    (rhsRun N betaN rows initial).2≤256*(j+1)*(d+1) := by
  have hh := GeneralPaperUnitArrayReprice.work 1 (fun i : Fin j =>
    ((N:ℤ)*(rows.read i).constant+betaN*(rows.read i).slope-
      (GeneralPaperBasisIntegerDot.run (rows.read i).coefficients.read (tailVector j initial)).value,
        (GeneralPaperBasisIntegerDot.run (rows.read i).coefficients.read (tailVector j initial)).work+12))
  change (rhsRun N betaN rows initial).2=(GeneralPaperBasisFreshRHS.rhsRun N betaN rows initial).2+8*j+2 at hh
  have ho := GeneralPaperBasisFreshRHS.rhs_work N betaN rows initial
  nlinarith only [hh,ho,Nat.zero_le (j*d)]

def divideRun {j : ℕ} (N : ℕ) (D : ℤ) (numerators : Vector j) : GeneralPaperBasisRationalSolve.RatVector j × ℕ :=
  PaperIndexedArrayConstruction.run (fun _ => 1) 1 (fun i => ((numerators.read i:ℚ)/((N:ℚ)*(D:ℚ)),12))

theorem divide_data {j : ℕ} (N : ℕ) (D : ℤ) (numerators : Vector j) :
    (divideRun N D numerators).1=(GeneralPaperBasisRationalSolve.divideRun N D numerators).1 := by
  simp only [divideRun,GeneralPaperBasisRationalSolve.divideRun,PaperIndexedArrayConstruction.run_data]

theorem divide_work {j : ℕ} (N : ℕ) (D : ℤ) (numerators : Vector j) : (divideRun N D numerators).2≤128*(j+1) := by
  have hh := GeneralPaperUnitArrayReprice.work 1 (fun i : Fin j => ((numerators.read i:ℚ)/((N:ℚ)*(D:ℚ)),12))
  change (divideRun N D numerators).2=(GeneralPaperBasisRationalSolve.divideRun N D numerators).2+8*j+2 at hh
  have ho := GeneralPaperBasisRationalSolve.divide_work N D numerators
  omega

def run {j : ℕ} (N : ℕ) (D : ℤ) (A : IntMatrix j) (rhs : Vector j) : GeneralPaperBasisRationalSolve.Result j :=
  let numerators := GeneralPaperBasisProductsWork.mulVecRun A rhs
  let values := divideRun N D numerators.1
  ⟨values.1,numerators.2+values.2+8⟩

theorem data {j : ℕ} (N : ℕ) (D : ℤ) (A : IntMatrix j) (rhs : Vector j) :
    (run N D A rhs).values=(GeneralPaperBasisRationalSolve.run N D A rhs).values := by
  simp only [run,GeneralPaperBasisRationalSolve.run,GeneralPaperBasisProductsWork.mulVec_data,divide_data]

theorem work {j : ℕ} (N : ℕ) (D : ℤ) (A : IntMatrix j) (rhs : Vector j) : (run N D A rhs).work≤512*(j+1)^2 := by
  have hm := GeneralPaperBasisProductsWork.mulVec_work A rhs
  have hd := divide_work N D (GeneralPaperBasisProductsWork.mulVecRun A rhs).1
  change _+(divideRun N D (GeneralPaperBasisProductsWork.mulVecRun A rhs).1).2+8≤_
  nlinarith only [hm,hd]

end Blotto.GeneralPaperBasisSolveWork
