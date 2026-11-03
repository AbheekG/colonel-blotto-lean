import Blotto.RationalPRGAccuracySampler
import Blotto.BudgetScalingRegret

/-! Ordered original rational budgets normalize to the verified PRG input.
The original promise 2 a v_j ≤ b is checked using rational comparisons. -/

namespace Blotto
open scoped BigOperators

structure RationalPRGOriginalInput (n : ℕ) where
  values : Fin n → ℚ
  positive : ∀ j, 0 < values j
  normalized : (∑ j, values j) = 1
  a : ℚ
  b : ℚ
  a_pos : 0 < a
  b_pos : 0 < b
  b_le : b ≤ a
  small_fields : ∀ j, 2 * a * values j ≤ b

namespace RationalPRGOriginalInput

noncomputable def realValues {n : ℕ} (i : RationalPRGOriginalInput n) : Values n :=
  ⟨fun j => (i.values j : ℝ), fun j => by exact_mod_cast i.positive j, by exact_mod_cast i.normalized⟩

def normalizedInput {n : ℕ} (i : RationalPRGOriginalInput n) : RationalPRGInput n where
  values := i.values
  positive := i.positive
  normalized := i.normalized
  b := i.b / i.a
  b_pos := div_pos i.b_pos i.a_pos
  b_le := (div_le_one i.a_pos).mpr i.b_le
  small_fields := fun j => (le_div_iff₀ i.a_pos).mpr (by nlinarith [i.small_fields j])

theorem normalized_values {n : ℕ} (i : RationalPRGOriginalInput n) : i.normalizedInput.real.values = i.realValues := rfl

theorem rescaled_poor_budget {n : ℕ} (i : RationalPRGOriginalInput n) :
    (i.a : ℝ) * (i.normalizedInput.b : ℝ) = (i.b : ℝ) := by
  change (i.a : ℝ) * ((i.b / i.a : ℚ) : ℝ) = (i.b : ℝ)
  rw [Rat.cast_div]
  have ha : (i.a : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt i.a_pos
  field_simp

end RationalPRGOriginalInput
end Blotto
