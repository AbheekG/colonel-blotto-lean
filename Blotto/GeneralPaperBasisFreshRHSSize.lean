import Blotto.GeneralPaperStoredProductSize

/-! The native fresh RHS uses the fixed original grid, never a previous
ray point. Its integer numerator bound is polynomial in N, the auxiliary
numerator and the dimension. The complete bit/space ledger is separate.
-/
namespace Blotto.GeneralPaperBasisFreshRHSSize
open GeneralPaperBasisStoredProducts GeneralPaperBasisFreshRHS GeneralPaperBasisInvariant
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 4500000

def bound (m K N B : ℕ) : ℕ := (m+1)*(N+B+m*(K-1)*N)

theorem rhs {T m K j : ℕ} (hm : 0<m) (dict : GeneralPaperDictionary.Dictionary T m K)
    (v : RationalFieldSelector m) (S h N : ℕ) (betaN : ℤ) (initialGrid : Vector (m*(K-1)))
    (hj : j≤m*(K-1)) (state : GeneralPaperBasisState.State j (m*(K-1)))
    (inv : Invariant dict v S h N betaN initialGrid hj state) (B : ℕ) (hB : betaN.natAbs≤B)
    (hGrid : ∀ a,(initialGrid.read a).natAbs≤N) (i : Fin j) :
    ((rhsRun N betaN state.rows initialGrid).1.read i).natAbs≤bound m K N B := by
  have hc := GeneralPaperBasisRowSize.rhs_entry hm dict v S h N betaN initialGrid hj state inv i false
  have hs := GeneralPaperBasisRowSize.rhs_entry hm dict v S h N betaN initialGrid hj state inv i true
  change (state.rows.read i).constant.natAbs≤m+1 at hc
  change (state.rows.read i).slope.natAbs≤m+1 at hs
  have ht := GeneralPaperIntegerDotSize.run_bound (state.rows.read i).coefficients.read (tailVector j initialGrid)
    (m+1) N (GeneralPaperBasisRowSize.coefficient hm dict v S h N betaN initialGrid hj state inv i) (fun a => by
      by_cases ha : j≤a.val
      · simpa only [tailVector,ha,ite_true] using hGrid a
      · simp only [tailVector,ha,ite_false,Int.natAbs_zero]
        exact Nat.zero_le _)
  have ht' : (∑ a : Fin (m*(K-1)),if j≤a.val then (state.rows.read i).coefficients.read a*initialGrid.read a else 0).natAbs≤
      m*(K-1)*(m+1)*N := by
    simpa only [GeneralPaperBasisIntegerDot.run_value,tailVector,mul_ite,mul_zero] using ht
  have hNterm : ((N:ℤ)*(state.rows.read i).constant).natAbs≤N*(m+1) := by
    rw [Int.natAbs_mul,Int.natAbs_natCast]
    exact Nat.mul_le_mul_left N hc
  have hBterm : (betaN*(state.rows.read i).slope).natAbs≤B*(m+1) := by
    rw [Int.natAbs_mul]
    exact Nat.mul_le_mul hB hs
  rw [rhs_data]
  have hSub := Int.natAbs_add_le ((N:ℤ)*(state.rows.read i).constant+betaN*(state.rows.read i).slope)
    (-(∑ a : Fin (m*(K-1)),if j≤a.val then (state.rows.read i).coefficients.read a*initialGrid.read a else 0))
  simp only [←sub_eq_add_neg,Int.natAbs_neg] at hSub
  have hAdd := Int.natAbs_add_le ((N:ℤ)*(state.rows.read i).constant) (betaN*(state.rows.read i).slope)
  unfold bound
  nlinarith only [hSub,hAdd,hNterm,hBterm,ht']

end Blotto.GeneralPaperBasisFreshRHSSize
