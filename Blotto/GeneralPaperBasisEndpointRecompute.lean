import Blotto.GeneralPaperBasisStageLattice

/-! The next freshly solved point is exactly the preceding ray endpoint.
Only original retained row data and the fixed grid are used at runtime;
the temporary endpoint's denominators are discarded.
-/
namespace Blotto.GeneralPaperBasisEndpointRecompute
open GeneralPaperBasisStoredProducts GeneralPaperBasisFreshRHS GeneralPaperBasisDenseRow
open GeneralPaperBasisFreshPointSound GeneralPaperBasisStoredCorrect GeneralPaperBasisAppendRows
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 3500000

theorem row_linear {d : ℕ} (r : Dense d) (x w : Fin d → ℝ) (t : ℝ) :
    rowValue r (fun k => x k+t*w k)=rowValue r x+t*rowValue r w := by
  simp only [rowValue,mul_add,Finset.sum_add_distrib,Finset.mul_sum]
  apply congrArg ((∑ k : Fin d,(r.coefficients.read k:ℝ)*x k)+·)
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem recompute {j d : ℕ} (N : ℕ) (hN : 0<N) (betaN D : ℤ) (hD : D≠0) (A : IntMatrix j)
    (rows : Rows j d) (initial : Vector d) (next : Fin d) (hNext : next.val=j)
    (hj : j≤d) (hNew : j+1≤d) (hValid : Valid D A (minor rows hj))
    (new : Dense d) (t : ℝ)
    (hTight : rowValue new (fun k => values N betaN D A rows initial k+
      t*GeneralPaperBasisDirectionSound.values D A rows next k)=bound new N betaN)
    (D' : ℤ) (hD' : D'≠0) (A' : IntMatrix (j+1))
    (hValid' : Valid D' A' (minor (append rows new) hNew)) :
    values N betaN D' A' (append rows new) initial=
      fun k => values N betaN D A rows initial k+t*GeneralPaperBasisDirectionSound.values D A rows next k := by
  symm
  apply GeneralPaperBasisFreshPointUnique.unique N hN betaN D' hD' A' (append rows new) initial hNew hValid'
  · intro i
    by_cases hi : i.val<j
    · let k : Fin j := ⟨i.val,hi⟩
      have he : i=k.castSucc := Fin.ext rfl
      rw [he,old_read,row_linear,retained_rows N hN betaN D hD A rows initial hj hValid k,
        GeneralPaperBasisDirectionSound.retained_zero D hD A rows next hNext hj hValid k,mul_zero,add_zero]
    · have he : i=GeneralPaperBasisAppendIndex.encode j none := by
        apply Fin.ext
        change i.val=j
        have hb := i.isLt
        omega
      rw [he,last_read]
      exact hTight
  · intro k hk
    have hOld : j≤k.val := by omega
    have hStrict : j<k.val := by omega
    simp only [values,GeneralPaperBasisFreshPoint.later_read N betaN D A rows initial k hOld,
      GeneralPaperBasisDirectionSound.values,GeneralPaperBasisDirection.later_read D A rows next k hStrict,
      Rat.cast_div,Rat.cast_intCast,Rat.cast_natCast,Rat.cast_zero,mul_zero,add_zero]

end Blotto.GeneralPaperBasisEndpointRecompute
