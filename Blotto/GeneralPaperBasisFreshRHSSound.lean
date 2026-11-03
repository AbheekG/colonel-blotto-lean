import Blotto.GeneralPaperBasisRationalSolveSound

/-! Exact real meaning of the original N-scaled right-hand side. The
fixed later coordinates are decoded only from their original grid words.
-/
namespace Blotto.GeneralPaperBasisFreshRHSSound
open GeneralPaperBasisStoredProducts GeneralPaperBasisFreshRHS
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 3000000

theorem rhs_real {j d : ℕ} (N : ℕ) (hN : 0<N) (betaN : ℤ) (rows : Rows j d) (initial : Vector d) (i : Fin j) :
    ((rhsRun N betaN rows initial).1.read i:ℝ)/(N:ℝ)=
      ((rows.read i).constant:ℝ)+((betaN:ℝ)/(N:ℝ))*((rows.read i).slope:ℝ)-
        ∑ k : Fin d,if j≤k.val then ((rows.read i).coefficients.read k:ℝ)*((initial.read k:ℝ)/(N:ℝ)) else 0 := by
  rw [rhs_data]
  simp only [Int.cast_sub,Int.cast_add,Int.cast_mul,Int.cast_natCast,Int.cast_sum,Int.cast_ite,Int.cast_zero]
  have hn : (N:ℝ)≠0 := by exact_mod_cast hN.ne'
  have hTail : (∑ k : Fin d,if j≤k.val then ((rows.read i).coefficients.read k:ℝ)*(initial.read k:ℝ) else 0)/(N:ℝ)=
      ∑ k : Fin d,if j≤k.val then ((rows.read i).coefficients.read k:ℝ)*((initial.read k:ℝ)/(N:ℝ)) else 0 := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hk : j≤k.val
    · simp only [hk,ite_true]
      ring
    · simp only [hk,ite_false,zero_div]
  rw [sub_div,add_div,hTail,mul_div_cancel_left₀ _ hn]
  ring

end Blotto.GeneralPaperBasisFreshRHSSound
