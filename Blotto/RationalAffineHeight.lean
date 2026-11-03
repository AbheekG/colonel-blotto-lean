import Blotto.RationalAffineAllocation
import Blotto.RationalLotteryHeight
import Blotto.RationalHeightBudget

/-! Actual native split and reflection maps have fixed-depth output heights.
The semantic identities include every coordinate of the stored affine matrix. -/

namespace Blotto.RationalAffineAllocation

theorem splitFirstTwo_value (a d : ℚ) (x : Fin 3 → ℚ) :
    (splitFirstTwo a d).value x = ![a / (a + d) * x 0, d / (a + d) * x 0, x 1, x 2] := by
  funext j
  fin_cases j <;> simp [splitFirstTwo, value, Fin.sum_univ_succ]

theorem reflectAppend_value (length x : Fin 3 → ℚ) :
    (reflectAppend length).value x = ![length 0 - x 0, length 1 - x 1, length 2 - x 2, 0] := by
  funext j
  fin_cases j <;> simp [reflectAppend, value, Fin.sum_univ_succ] <;> ring

theorem splitFirstTwo_height (a d : ℚ) (x : Fin 3 → ℚ) (s : ℕ)
    (hA : RationalHeight a s) (hD : RationalHeight d s) (hX : ∀ j, RationalHeight (x j) s) (j : Fin 4) :
    RationalHeight ((splitFirstTwo a d).value x j) (expressionHeightBudget s 3) := by
  have hA0 : RationalHeight a (expressionHeightBudget s 0) := by simpa only [expressionHeightBudget_zero] using hA
  have hD0 : RationalHeight d (expressionHeightBudget s 0) := by simpa only [expressionHeightBudget_zero] using hD
  have hSum := hA0.add_level hD0
  have hm1 := expressionHeightBudget_ge_input s 1
  have hm2 := expressionHeightBudget_ge_input s 2
  have hRatioA := (hA.mono hm1).div_level hSum
  have hRatioD := (hD.mono hm1).div_level hSum
  rw [splitFirstTwo_value]
  fin_cases j
  · exact hRatioA.mul_level ((hX 0).mono hm2)
  · exact hRatioD.mul_level ((hX 0).mono hm2)
  · exact (hX 1).mono (expressionHeightBudget_ge_input s 3)
  · exact (hX 2).mono (expressionHeightBudget_ge_input s 3)

theorem reflectAppend_height (length x : Fin 3 → ℚ) (s : ℕ) (hs : 2 ≤ s)
    (hL : ∀ j, RationalHeight (length j) s) (hX : ∀ j, RationalHeight (x j) s) (j : Fin 4) :
    RationalHeight ((reflectAppend length).value x j) (expressionHeightBudget s 1) := by
  have hDiff : ∀ j, RationalHeight (length j - x j) (expressionHeightBudget s 1) := by
    intro k
    have hL0 : RationalHeight (length k) (expressionHeightBudget s 0) := by simpa only [expressionHeightBudget_zero] using hL k
    have hX0 : RationalHeight (x k) (expressionHeightBudget s 0) := by simpa only [expressionHeightBudget_zero] using hX k
    exact hL0.sub_level hX0
  rw [reflectAppend_value]
  fin_cases j
  · exact hDiff 0
  · exact hDiff 1
  · exact hDiff 2
  · exact (show RationalHeight (0 : ℚ) 2 by norm_num [RationalHeight]).mono (hs.trans (expressionHeightBudget_ge_input s 1))

end Blotto.RationalAffineAllocation

namespace Blotto.RationalSegmentLottery

theorem HeightAt.mapped_split {k : ℕ} {l : RationalSegmentLottery 3 k} {s : ℕ} (h : l.HeightAt s)
    (a d : ℚ) (hA : RationalHeight a s) (hD : RationalHeight d s) :
    (l.mapped (RationalAffineAllocation.splitFirstTwo a d)).HeightAt (expressionHeightBudget s 3) := by
  constructor
  · intro slot; exact (h.1 slot).mono (expressionHeightBudget_ge_input s 3)
  · intro slot j
    exact ⟨RationalAffineAllocation.splitFirstTwo_height a d (l.P slot) s hA hD (fun r => (h.2 slot r).1) j,
      RationalAffineAllocation.splitFirstTwo_height a d (l.Q slot) s hA hD (fun r => (h.2 slot r).2) j⟩

end Blotto.RationalSegmentLottery
