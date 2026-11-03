import Blotto.RationalAffineAllocation

/-! Box/budget contracts for the native splitting and reflection matrices.
Reflection requires the original box on every path, rather than merely an
almost-sure budget statement. -/

namespace Blotto.RationalAffineAllocation

theorem splitFirstTwo_box (a d : ℚ) (ha : 0 < a) (hd : 0 < d) {c ell : ℝ} {x : Allocation 3}
    (hx : InBox ![((a + d : ℚ) : ℝ), c, ell] x) :
    InBox ![(a : ℝ), (d : ℝ), c, ell] ((splitFirstTwo a d).real.value x) := by
  rw [splitFirstTwo_real]
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hsum : (0 : ℝ) < (a : ℝ) + (d : ℝ) := add_pos haR hdR
  have hx0 : 0 ≤ x 0 ∧ x 0 ≤ (a : ℝ) + (d : ℝ) := by
    simpa only [Rat.cast_add, Matrix.cons_val_zero] using hx 0
  intro j
  fin_cases j
  · change 0 ≤ (a : ℝ) / ((a : ℝ) + (d : ℝ)) * x 0 ∧
      (a : ℝ) / ((a : ℝ) + (d : ℝ)) * x 0 ≤ (a : ℝ)
    constructor
    · exact mul_nonneg (div_nonneg (le_of_lt haR) (le_of_lt hsum)) hx0.1
    · calc
        _ ≤ (a : ℝ) / ((a : ℝ) + (d : ℝ)) * ((a : ℝ) + (d : ℝ)) :=
          mul_le_mul_of_nonneg_left hx0.2 (div_nonneg (le_of_lt haR) (le_of_lt hsum))
        _ = _ := div_mul_cancel₀ _ (ne_of_gt hsum)
  · change 0 ≤ (d : ℝ) / ((a : ℝ) + (d : ℝ)) * x 0 ∧
      (d : ℝ) / ((a : ℝ) + (d : ℝ)) * x 0 ≤ (d : ℝ)
    constructor
    · exact mul_nonneg (div_nonneg (le_of_lt hdR) (le_of_lt hsum)) hx0.1
    · calc
        _ ≤ (d : ℝ) / ((a : ℝ) + (d : ℝ)) * ((a : ℝ) + (d : ℝ)) :=
          mul_le_mul_of_nonneg_left hx0.2 (div_nonneg (le_of_lt hdR) (le_of_lt hsum))
        _ = _ := div_mul_cancel₀ _ (ne_of_gt hsum)
  · exact hx 1
  · exact hx 2

theorem reflectAppend_fullBudget (length : Fin 3 → ℚ) {B M : ℝ} {x : Allocation 3}
    (hS : (∑ j, (length j : ℝ)) = B + M) (hB : FullBudget M x)
    (hbox : InBox (fun j => (length j : ℝ)) x) :
    FullBudget B ((reflectAppend length).real.value x) := by
  rw [reflectAppend_real]
  exact Blotto.reflectAppend_fullBudget hS hB hbox

theorem reflectAppend_box (length : Fin 3 → ℚ) {ell : ℝ} (he : 0 ≤ ell) {x : Allocation 3}
    (hbox : InBox (fun j => (length j : ℝ)) x) :
    InBox ![(length 0 : ℝ), (length 1 : ℝ), (length 2 : ℝ), ell] ((reflectAppend length).real.value x) := by
  rw [reflectAppend_real]
  intro j
  fin_cases j
  · change 0 ≤ (length 0 : ℝ) - x 0 ∧ (length 0 : ℝ) - x 0 ≤ (length 0 : ℝ)
    constructor <;> linarith [(hbox 0).1, (hbox 0).2]
  · change 0 ≤ (length 1 : ℝ) - x 1 ∧ (length 1 : ℝ) - x 1 ≤ (length 1 : ℝ)
    constructor <;> linarith [(hbox 1).1, (hbox 1).2]
  · change 0 ≤ (length 2 : ℝ) - x 2 ∧ (length 2 : ℝ) - x 2 ≤ (length 2 : ℝ)
    constructor <;> linarith [(hbox 2).1, (hbox 2).2]
  · exact ⟨le_rfl, he⟩

end Blotto.RationalAffineAllocation
