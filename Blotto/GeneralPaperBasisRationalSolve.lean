import Blotto.GeneralPaperBasisFreshRHS

/-! Native fresh rational prefix solve using the retained integer adjugate.
All coordinates share N*D before reduction; no earlier point denominator
enters the computation.
-/
namespace Blotto.GeneralPaperBasisRationalSolve
open GeneralPaperBasisStoredProducts
set_option autoImplicit false
set_option maxHeartbeats 3000000

abbrev RatVector (j : ℕ) := FixedArrayTable j ℚ

structure Result (j : ℕ) where
  values : RatVector j
  work : ℕ

def divideRun {j : ℕ} (N : ℕ) (D : ℤ) (numerators : Vector j) : RatVector j × ℕ :=
  PaperIndexedArrayConstruction.run (fun _ => 0) 1 (fun i => ((numerators.read i:ℚ)/((N:ℚ)*(D:ℚ)),12))

def run {j : ℕ} (N : ℕ) (D : ℤ) (A : IntMatrix j) (rhs : Vector j) : Result j :=
  let numerators := mulVecRun A rhs
  let values := divideRun N D numerators.1
  ⟨values.1,numerators.2+values.2+8⟩

theorem read {j : ℕ} (N : ℕ) (D : ℤ) (A : IntMatrix j) (rhs : Vector j) (i : Fin j) :
    (run N D A rhs).values.read i=(((observe A).mulVec rhs.read i:ℤ):ℚ)/((N:ℚ)*(D:ℚ)) := by
  simp only [run,divideRun,PaperIndexedArrayConstruction.run_data,FixedArrayTable.read_ofFn,mulVec_data]

theorem lattice {j : ℕ} (N : ℕ) (hN : 0<N) (D : ℤ) (hD : D≠0) (A : IntMatrix j) (rhs : Vector j) (i : Fin j) :
    OnRationalLattice (N*D.natAbs) ((run N D A rhs).values.read i) := by
  rw [read]
  have hn : (N:ℤ)≠0 := by exact_mod_cast hN.ne'
  have hh := FinitePolytopeRationalWitness.denominator_divInt
    (numerator := (observe A).mulVec rhs.read i) (denominator := (N:ℤ)*D) (mul_ne_zero hn hD)
  simpa [OnRationalLattice,Int.cast_mul,Int.natAbs_mul] using hh

theorem divide_work {j : ℕ} (N : ℕ) (D : ℤ) (numerators : Vector j) : (divideRun N D numerators).2≤64*(j+1) := by
  have hh := PaperIndexedArrayConstruction.run_work_bound (fun _ => 0) 0 (fun _ => by simp) 1
    (fun i : Fin j => ((numerators.read i:ℚ)/((N:ℚ)*(D:ℚ)),12))
  simp only [Finset.sum_const,Finset.card_fin,nsmul_eq_mul,Nat.cast_id,Nat.mul_zero,Nat.zero_mul,Nat.add_zero] at hh
  change (divideRun N D numerators).2≤_ at hh
  omega

theorem work {j : ℕ} (N : ℕ) (D : ℤ) (A : IntMatrix j) (rhs : Vector j) : (run N D A rhs).work≤256*(j+1)^2 := by
  have hm := mulVec_work A rhs
  have hd := divide_work N D (mulVecRun A rhs).1
  change (mulVecRun A rhs).2+(divideRun N D (mulVecRun A rhs).1).2+8≤_
  nlinarith only [hm,hd]

end Blotto.GeneralPaperBasisRationalSolve
