import Blotto.GeneralPaperBasisRationalSolve

/-! Actual fresh current-point construction. Original-row RHS numerators
and the retained cache solve the first j coordinates; every later value
comes from the fixed original N-grid vector.
-/
namespace Blotto.GeneralPaperBasisFreshPoint
open GeneralPaperBasisStoredProducts GeneralPaperBasisFreshRHS GeneralPaperBasisPrefixSum
set_option autoImplicit false
set_option maxHeartbeats 3000000

def assemble {j d : ℕ} (N : ℕ) (first : GeneralPaperBasisRationalSolve.RatVector j) (initial : Vector d) :
    GeneralPaperBasisRationalSolve.RatVector d × ℕ :=
  PaperIndexedArrayConstruction.run (fun _ => 0) 1 (fun k =>
    (if h : k.val<j then first.read ⟨k.val,h⟩ else (initial.read k:ℚ)/(N:ℚ),16))

structure Result (d : ℕ) where
  point : GeneralPaperBasisRationalSolve.RatVector d
  work : ℕ

def run {j d : ℕ} (N : ℕ) (betaN D : ℤ) (A : IntMatrix j) (rows : Rows j d) (initial : Vector d) : Result d :=
  let rhs := rhsRun N betaN rows initial
  let first := GeneralPaperBasisRationalSolve.run N D A rhs.1
  let point := assemble N first.values initial
  ⟨point.1,rhs.2+first.work+point.2+12⟩

theorem first_read {j d : ℕ} (N : ℕ) (betaN D : ℤ) (A : IntMatrix j) (rows : Rows j d) (initial : Vector d)
    (hj : j≤d) (i : Fin j) :
    (run N betaN D A rows initial).point.read (embed hj i)=
      (((observe A).mulVec (rhsRun N betaN rows initial).1.read i:ℤ):ℚ)/((N:ℚ)*(D:ℚ)) := by
  simp only [run,assemble,PaperIndexedArrayConstruction.run_data,FixedArrayTable.read_ofFn]
  change (if h : i.val<j then (GeneralPaperBasisRationalSolve.run N D A (rhsRun N betaN rows initial).1).values.read ⟨i.val,h⟩ else _)=_
  rw [dite_eq_left i.isLt]
  exact GeneralPaperBasisRationalSolve.read N D A _ i

theorem later_read {j d : ℕ} (N : ℕ) (betaN D : ℤ) (A : IntMatrix j) (rows : Rows j d) (initial : Vector d)
    (k : Fin d) (hk : j≤k.val) : (run N betaN D A rows initial).point.read k=(initial.read k:ℚ)/(N:ℚ) := by
  simp only [run,assemble,PaperIndexedArrayConstruction.run_data,FixedArrayTable.read_ofFn]
  rw [dite_eq_right (show ¬k.val<j by omega)]

theorem assemble_work {j d : ℕ} (N : ℕ) (first : GeneralPaperBasisRationalSolve.RatVector j) (initial : Vector d) :
    (assemble N first initial).2≤64*(d+1) := by
  have hh := PaperIndexedArrayConstruction.run_work_bound (fun _ => 0) 0 (fun _ => by simp) 1
    (fun k : Fin d => (if h : k.val<j then first.read ⟨k.val,h⟩ else (initial.read k:ℚ)/(N:ℚ),16))
  simp only [Finset.sum_const,Finset.card_fin,nsmul_eq_mul,Nat.cast_id,Nat.mul_zero,Nat.zero_mul,Nat.add_zero] at hh
  change (assemble N first initial).2≤_ at hh
  omega

theorem work {j d : ℕ} (N : ℕ) (betaN D : ℤ) (A : IntMatrix j) (rows : Rows j d) (initial : Vector d) :
    (run N betaN D A rows initial).work≤512*(j+1)*(j+d+2) := by
  have hr := rhs_work N betaN rows initial
  have hs := GeneralPaperBasisRationalSolve.work N D A (rhsRun N betaN rows initial).1
  have ha := assemble_work N (GeneralPaperBasisRationalSolve.run N D A (rhsRun N betaN rows initial).1).values initial
  change (rhsRun N betaN rows initial).2+(GeneralPaperBasisRationalSolve.run N D A (rhsRun N betaN rows initial).1).work+
    (assemble N (GeneralPaperBasisRationalSolve.run N D A (rhsRun N betaN rows initial).1).values initial).2+12≤_
  nlinarith only [hr,hs,ha]

end Blotto.GeneralPaperBasisFreshPoint
