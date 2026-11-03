import Blotto.GeneralPaperBasisDirection

/-! Exact direction evaluation on every retained or new dense row. The
actual cached solve annihilates all old rows, while the next coordinate
has velocity one and all later coordinates have velocity zero.
-/
namespace Blotto.GeneralPaperBasisDirectionSound
open GeneralPaperBasisStoredProducts GeneralPaperBasisFreshRHS GeneralPaperBasisPrefixSum
open GeneralPaperBasisIntegerCasts GeneralPaperBasisStoredCorrect GeneralPaperBasisDirection
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 3500000

noncomputable def values {j d : ℕ} (D : ℤ) (A : IntMatrix j) (rows : Rows j d) (next : Fin d) : Fin d → ℝ :=
  fun k => ((run D A rows next).velocity.read k:ℝ)

noncomputable def solved {j d : ℕ} (D : ℤ) (A : IntMatrix j) (rows : Rows j d) (next : Fin d) : Fin j → ℝ :=
  fun i => ((GeneralPaperBasisRationalSolve.run 1 D A (columnRun rows next).1).values.read i:ℝ)

theorem dot {j d : ℕ} (D : ℤ) (A : IntMatrix j) (rows : Rows j d) (next : Fin d) (hNext : next.val=j)
    (hj : j≤d) (v : Vector d) :
    (∑ k : Fin d,(v.read k:ℝ)*values D A rows next k)=
      (v.read next:ℝ)-∑ i : Fin j,(v.read (embed hj i):ℝ)*solved D A rows next i := by
  rw [split_sum hj]
  have hFirst : (∑ i : Fin j,(v.read (embed hj i):ℝ)*values D A rows next (embed hj i))=
      -(∑ i : Fin j,(v.read (embed hj i):ℝ)*solved D A rows next i) := by
    simp only [values,first_read D A rows next hj,Rat.cast_neg,mul_neg,Finset.sum_neg_distrib,solved]
  have hTail : (∑ k : Fin d,if j≤k.val then (v.read k:ℝ)*values D A rows next k else 0)=(v.read next:ℝ) := by
    calc
      _ = (if j≤next.val then (v.read next:ℝ)*values D A rows next next else 0) := by
        apply Finset.sum_eq_single next
        · intro k _ hk
          by_cases hLow : j≤k.val
          · have hNe : k.val≠j := fun he => hk (Fin.ext (he.trans hNext.symm))
            have hStrict : j<k.val := by omega
            simp only [hLow,ite_true,values,later_read D A rows next k hStrict,Rat.cast_zero,mul_zero]
          · simp only [hLow,ite_false]
        · intro hNot
          exact (hNot (Finset.mem_univ _)).elim
      _ = _ := by simp only [hNext,Nat.le_refl,ite_true,values,next_read D A rows next hNext,Rat.cast_one,mul_one]
  rw [hFirst,hTail]
  ring

theorem solved_system {j d : ℕ} (D : ℤ) (hD : D≠0) (A : IntMatrix j) (rows : Rows j d)
    (next : Fin d) (hj : j≤d) (hValid : Valid D A (minor rows hj)) :
    (realMatrix (minor rows hj)).mulVec (solved D A rows next)=realVector (columnRun rows next).1.read := by
  have hh := GeneralPaperBasisRationalSolveSound.system 1 (by decide) D hD A (minor rows hj) hValid (columnRun rows next).1
  unfold solved realVector
  simpa only [Nat.cast_one,div_one] using hh

theorem retained_zero {j d : ℕ} (D : ℤ) (hD : D≠0) (A : IntMatrix j) (rows : Rows j d)
    (next : Fin d) (hNext : next.val=j) (hj : j≤d) (hValid : Valid D A (minor rows hj)) (i : Fin j) :
    GeneralPaperBasisFreshPointSound.rowValue (rows.read i) (values D A rows next)=0 := by
  have hh := congrFun (solved_system D hD A rows next hj hValid) i
  change (∑ k : Fin j,((rows.read i).coefficients.read (embed hj k):ℝ)*solved D A rows next k)=
    ((columnRun rows next).1.read i:ℝ) at hh
  rw [column_read] at hh
  unfold GeneralPaperBasisFreshPointSound.rowValue
  rw [dot D A rows next hNext hj (rows.read i).coefficients,hh,sub_self]

end Blotto.GeneralPaperBasisDirectionSound
