import Blotto.RationalLottoResourceSystem

/-! The manuscript's global exhaustion row (B,0,...,0). Constructing this
coordinate function requires no path traversal or coupling compilation. -/

namespace Blotto.RationalLottoResourceSystem
open scoped BigOperators

theorem fieldCount_pos {n : ℕ} (i : RationalLottoResourceSystem n) : 0 < n := by
  by_contra h
  have hn : n = 0 := by omega
  subst n
  have hs := i.initial_sum
  simp only [Finset.univ_eq_empty, Finset.sum_empty] at hs
  linarith [i.B_pos]

def firstField {n : ℕ} (i : RationalLottoResourceSystem n) : Fin n := ⟨0, i.fieldCount_pos⟩

def fallbackAllocation {n : ℕ} (i : RationalLottoResourceSystem n) : Fin n → ℚ :=
  fun j => if j = i.firstField then i.B else 0

theorem fallbackAllocation_first {n : ℕ} (i : RationalLottoResourceSystem n) : i.fallbackAllocation i.firstField = i.B := by
  simp [fallbackAllocation]

theorem fallbackAllocation_other {n : ℕ} (i : RationalLottoResourceSystem n) (j : Fin n) (hj : j ≠ i.firstField) :
    i.fallbackAllocation j = 0 := by simp [fallbackAllocation, hj]

theorem fallbackAllocation_fullBudget {n : ℕ} (i : RationalLottoResourceSystem n) :
    FullBudget (i.B : ℝ) (fun j => (i.fallbackAllocation j : ℝ)) := by
  constructor
  · intro j
    change (0 : ℝ) ≤ ((if j = i.firstField then i.B else 0 : ℚ) : ℝ)
    by_cases hj : j = i.firstField
    · rw [ite_eq_left hj]
      exact_mod_cast le_of_lt i.B_pos
    · rw [ite_eq_right hj]
      norm_num
  · have he : (fun j => (i.fallbackAllocation j : ℝ)) = fun j => if j = i.firstField then (i.B : ℝ) else 0 := by
      funext j
      by_cases hj : j = i.firstField <;> simp [fallbackAllocation, hj]
    rw [he]
    simp

end Blotto.RationalLottoResourceSystem
