import Blotto.GeneralPaperBasisFreshPointSound

/-! Fresh original-row solves identify the next stage point exactly with
any preceding feasible endpoint satisfying the same retained rows and
fixed tail. No feasibility or rationalization oracle is needed.
-/
namespace Blotto.GeneralPaperBasisFreshPointUnique
open GeneralPaperBasisStoredProducts GeneralPaperBasisFreshRHS GeneralPaperBasisPrefixSum
open GeneralPaperBasisFreshPointSound GeneralPaperBasisIntegerCasts GeneralPaperBasisStoredCorrect
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 3500000

theorem prefix_of_rows {j d : ℕ} (N : ℕ) (hN : 0<N) (betaN : ℤ) (rows : Rows j d) (initial : Vector d)
    (hj : j≤d) (x : Fin d → ℝ)
    (hRows : ∀ i,rowValue (rows.read i) x=bound (rows.read i) N betaN)
    (hLater : ∀ k,j≤k.val → x k=(initial.read k:ℝ)/(N:ℝ)) :
    (realMatrix (minor rows hj)).mulVec (fun k => x (embed hj k))=
      fun i => ((rhsRun N betaN rows initial).1.read i:ℝ)/(N:ℝ) := by
  funext i
  have hh := hRows i
  unfold rowValue bound at hh
  rw [split_sum hj] at hh
  have hTail : (∑ k : Fin d,if j≤k.val then ((rows.read i).coefficients.read k:ℝ)*x k else 0)=
      ∑ k : Fin d,if j≤k.val then ((rows.read i).coefficients.read k:ℝ)*((initial.read k:ℝ)/(N:ℝ)) else 0 := by
    apply Finset.sum_congr rfl
    intro k _
    by_cases hk : j≤k.val
    · simp only [hk,ite_true,hLater k hk]
    · simp only [hk,ite_false]
  rw [hTail] at hh
  change (∑ k : Fin j,((rows.read i).coefficients.read (embed hj k):ℝ)*x (embed hj k))=_
  rw [GeneralPaperBasisFreshRHSSound.rhs_real N hN betaN rows initial i]
  linarith only [hh]

theorem unique {j d : ℕ} (N : ℕ) (hN : 0<N) (betaN D : ℤ) (hD : D≠0) (A : IntMatrix j)
    (rows : Rows j d) (initial : Vector d) (hj : j≤d) (hValid : Valid D A (minor rows hj)) (x : Fin d → ℝ)
    (hRows : ∀ i,rowValue (rows.read i) x=bound (rows.read i) N betaN)
    (hLater : ∀ k,j≤k.val → x k=(initial.read k:ℝ)/(N:ℝ)) : x=values N betaN D A rows initial := by
  have hM : (realMatrix (minor rows hj)).det≠0 := by rw [←det_cast,←hValid.1]; exact_mod_cast hD
  have hX := prefix_of_rows N hN betaN rows initial hj x hRows hLater
  have hY := prefix_system N hN betaN D hD A rows initial hj hValid
  have hx := GeneralPaperBasisAdjugateSolve.unique_solution (realMatrix (minor rows hj)) _ _ hM hX
  have hy := GeneralPaperBasisAdjugateSolve.unique_solution (realMatrix (minor rows hj)) _ _ hM hY
  have hSame := hx.trans hy.symm
  funext k
  by_cases hk : k.val<j
  · exact congrFun hSame ⟨k.val,hk⟩
  · have hjk : j≤k.val := by omega
    rw [hLater k hjk]
    simp only [values,GeneralPaperBasisFreshPoint.later_read N betaN D A rows initial k hjk,
      Rat.cast_div,Rat.cast_intCast,Rat.cast_natCast]

end Blotto.GeneralPaperBasisFreshPointUnique
