import Blotto.GeneralPaperBasisFreshRHSSound

/-! The native fresh point satisfies every retained ORIGINAL packed row,
with later coordinates fixed at the initial N-grid values. Uniqueness
will identify it with the preceding feasible ray endpoint.
-/
namespace Blotto.GeneralPaperBasisFreshPointSound
open GeneralPaperBasisStoredProducts GeneralPaperBasisFreshRHS GeneralPaperBasisPrefixSum
open GeneralPaperBasisIntegerCasts GeneralPaperBasisStoredCorrect
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 3500000

noncomputable def values {j d : ℕ} (N : ℕ) (betaN D : ℤ) (A : IntMatrix j) (rows : Rows j d) (initial : Vector d) : Fin d → ℝ :=
  fun k => ((GeneralPaperBasisFreshPoint.run N betaN D A rows initial).point.read k:ℝ)

noncomputable def rowValue {d : ℕ} (row : GeneralPaperBasisDenseRow.Dense d) (x : Fin d → ℝ) : ℝ :=
  ∑ k,(row.coefficients.read k:ℝ)*x k

noncomputable def bound {d : ℕ} (row : GeneralPaperBasisDenseRow.Dense d) (N : ℕ) (betaN : ℤ) : ℝ :=
  (row.constant:ℝ)+((betaN:ℝ)/(N:ℝ))*(row.slope:ℝ)

theorem prefix_system {j d : ℕ} (N : ℕ) (hN : 0<N) (betaN D : ℤ) (hD : D≠0) (A : IntMatrix j)
    (rows : Rows j d) (initial : Vector d) (hj : j≤d) (hValid : Valid D A (minor rows hj)) :
    (realMatrix (minor rows hj)).mulVec (fun k => values N betaN D A rows initial (embed hj k))=
      fun i => ((rhsRun N betaN rows initial).1.read i:ℝ)/(N:ℝ) := by
  have hh := GeneralPaperBasisRationalSolveSound.system N hN D hD A (minor rows hj) hValid (rhsRun N betaN rows initial).1
  have hPoint (k : Fin j) : values N betaN D A rows initial (embed hj k)=
      ((GeneralPaperBasisRationalSolve.run N D A (rhsRun N betaN rows initial).1).values.read k:ℝ) := by
    simp only [values,GeneralPaperBasisFreshPoint.first_read,GeneralPaperBasisRationalSolve.read]
  simpa only [hPoint] using hh

theorem tail_sum {j d : ℕ} (N : ℕ) (betaN D : ℤ) (A : IntMatrix j) (rows : Rows j d) (initial : Vector d) (i : Fin j) :
    (∑ k : Fin d,if j≤k.val then ((rows.read i).coefficients.read k:ℝ)*values N betaN D A rows initial k else 0)=
      ∑ k : Fin d,if j≤k.val then ((rows.read i).coefficients.read k:ℝ)*((initial.read k:ℝ)/(N:ℝ)) else 0 := by
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : j≤k.val
  · simp only [hk,ite_true,values,GeneralPaperBasisFreshPoint.later_read N betaN D A rows initial k hk,Rat.cast_div,Rat.cast_intCast,Rat.cast_natCast]
  · simp only [hk,ite_false]

theorem retained_rows {j d : ℕ} (N : ℕ) (hN : 0<N) (betaN D : ℤ) (hD : D≠0) (A : IntMatrix j)
    (rows : Rows j d) (initial : Vector d) (hj : j≤d) (hValid : Valid D A (minor rows hj)) (i : Fin j) :
    rowValue (rows.read i) (values N betaN D A rows initial)=bound (rows.read i) N betaN := by
  have hh := congrFun (prefix_system N hN betaN D hD A rows initial hj hValid) i
  change (∑ k : Fin j,((rows.read i).coefficients.read (embed hj k):ℝ)*values N betaN D A rows initial (embed hj k))=
    ((rhsRun N betaN rows initial).1.read i:ℝ)/(N:ℝ) at hh
  unfold rowValue bound
  rw [split_sum hj,hh,tail_sum,GeneralPaperBasisFreshRHSSound.rhs_real N hN betaN rows initial i]
  ring

end Blotto.GeneralPaperBasisFreshPointSound
