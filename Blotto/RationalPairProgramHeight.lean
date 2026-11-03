import Blotto.RationalPairProgram
import Blotto.RationalResourceHeight
import Blotto.RationalExpressionWordWidth

open scoped BigOperators

/-! Every shared pair register has a fixed-depth rational height bound.
This connects the arithmetic-call model to operand sizes without charging a
resource-depth growth factor to the general source loop. -/

namespace Blotto.RationalPairProgram

theorem registers_height {p : RationalRoundingPair} {s : ℕ} (h : p.FieldsHeight s) (hs : 2 ≤ s) :
    ∀ j : Fin 12, RationalHeight ((run p).getD j.val 0) (expressionHeightBudget s 4) := by
  have hTotal : RationalHeight p.total (expressionHeightBudget s 1) := by
    exact (h.2.2.1.mono (expressionHeightBudget_ge_input s 0)).add_level
      (h.2.2.2.mono (expressionHeightBudget_ge_input s 0))
  have hDiff : RationalHeight (p.total - p.lengthJ) (expressionHeightBudget s 2) :=
    hTotal.sub_level (h.2.1.mono (expressionHeightBudget_ge_input s 1))
  have hEndpoints := h.endpoints hs
  have hNum : RationalHeight (p.resourceI - p.lower) (expressionHeightBudget s 3) :=
    (h.2.2.1.mono (expressionHeightBudget_ge_input s 2)).sub_level hEndpoints.1
  have hDen : RationalHeight (p.upper - p.lower) (expressionHeightBudget s 3) :=
    hEndpoints.2.sub_level hEndpoints.1
  have hProbability := h.probability hs
  have hZero : RationalHeight (0 : ℚ) (expressionHeightBudget s 4) :=
    (show RationalHeight (0 : ℚ) 2 by norm_num [RationalHeight]).mono
      (hs.trans (expressionHeightBudget_ge_input s 4))
  have hOneFour : expressionHeightBudget s 1 ≤ expressionHeightBudget s 4 := expressionHeightBudget_mono s (by decide)
  have hTwoFour : expressionHeightBudget s 2 ≤ expressionHeightBudget s 4 := expressionHeightBudget_mono s (by decide)
  have hThreeFour : expressionHeightBudget s 3 ≤ expressionHeightBudget s 4 := expressionHeightBudget_mono s (by decide)
  intro j
  fin_cases j <;> rw [run_eq]
  · exact h.1.mono (expressionHeightBudget_ge_input s 4)
  · exact h.2.1.mono (expressionHeightBudget_ge_input s 4)
  · exact h.2.2.1.mono (expressionHeightBudget_ge_input s 4)
  · exact h.2.2.2.mono (expressionHeightBudget_ge_input s 4)
  · exact hZero
  · exact hTotal.mono hOneFour
  · exact hDiff.mono hTwoFour
  · exact hEndpoints.1.mono hTwoFour
  · exact hEndpoints.2.mono hTwoFour
  · exact hNum.mono hThreeFour
  · exact hDen.mono hThreeFour
  · exact hProbability

theorem registers_wordWidth {p : RationalRoundingPair} {s : ℕ} (h : p.FieldsHeight s) (hs : 2 ≤ s) :
    ∀ j : Fin 12, rationalWordWidth ((run p).getD j.val 0) ≤ 32 * s + 31 := by
  intro j
  have hw := rationalWordWidth_of_height (registers_height h hs j)
  simp only [expressionHeightBudget, show (2 : ℕ) ^ 4 = 16 by decide] at hw
  omega

theorem twelve_sum_bound (f : Fin 12 → ℕ) (bound : ℕ) (hf : ∀ j, f j ≤ bound) :
    (∑ j : Fin 12, f j) ≤ 12 * bound := by
  have hSum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 12)))
    (f := f) (g := fun _ => bound) (fun j _ => hf j)
  have hConst : (∑ _j : Fin 12, bound) = 12 * bound := by simp
  exact hSum.trans_eq hConst

theorem total_register_wordWidth {p : RationalRoundingPair} {s : ℕ} (h : p.FieldsHeight s) (hs : 2 ≤ s) :
    (∑ j : Fin 12, rationalWordWidth ((run p).getD j.val 0)) ≤ 12 * (32 * s + 31) :=
  twelve_sum_bound (fun j => rationalWordWidth ((run p).getD j.val 0)) (32 * s + 31) (registers_wordWidth h hs)

end Blotto.RationalPairProgram
