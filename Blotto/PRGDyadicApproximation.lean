import Blotto.LottoResourceDyadic
import Blotto.PRGApproximation

/-! Both PRG whole laws with finite scalar draws have continuous Nash regret
at most 3/2^K and exact hard budgets. This is the midpoint stage only: exact
branch weights are retained, and bounded fair-bit branch access/costs remain
separate implementation obligations. -/

namespace Blotto.PRGInput
open MeasureTheory

noncomputable def richDyadicLaw {n : ℕ} (i : PRGInput n) (K : ℕ) : Mixed n := i.richSystem.dyadicLaw K
noncomputable def poorDyadicLaw {n : ℕ} (i : PRGInput n) (K : ℕ) : Mixed n := i.poorSystem.dyadicLaw K

theorem richDyadicLaw_CDF_error {n : ℕ} (i : PRGInput n) (K : ℕ) :
    CDFClose (i.richDyadicLaw K) i.richLaw (3 / (2 * (2 : ℝ) ^ K)) := i.richSystem.dyadicLaw_CDF_error K

theorem poorDyadicLaw_CDF_error {n : ℕ} (i : PRGInput n) (K : ℕ) :
    CDFClose (i.poorDyadicLaw K) i.poorLaw (3 / (2 * (2 : ℝ) ^ K)) := i.poorSystem.dyadicLaw_CDF_error K

theorem richDyadicLaw_fullBudget {n : ℕ} (i : PRGInput n) (K : ℕ) :
    ∀ᵐ x ∂(i.richDyadicLaw K : Measure (Allocation n)), FullBudget 1 x := i.richSystem.dyadicLaw_fullBudget K

theorem poorDyadicLaw_fullBudget {n : ℕ} (i : PRGInput n) (K : ℕ) :
    ∀ᵐ x ∂(i.poorDyadicLaw K : Measure (Allocation n)), FullBudget i.b x := i.poorSystem.dyadicLaw_fullBudget K

theorem dyadic_regrets {n : ℕ} (i : PRGInput n) (K : ℕ) :
    regret i.values 1 (i.richDyadicLaw K) (i.poorDyadicLaw K) ≤ 3 / (2 : ℝ) ^ K ∧
      regret i.values i.b (i.poorDyadicLaw K) (i.richDyadicLaw K) ≤ 3 / (2 : ℝ) ^ K := by
  have he := i.approximation_regrets _ _ (i.richSystem.dyadicLaw_supported K) (i.poorSystem.dyadicLaw_supported K)
    (i.richDyadicLaw_CDF_error K).symm (i.poorDyadicLaw_CDF_error K).symm
  have hr : 3 / (2 * (2 : ℝ) ^ K) + 3 / (2 * (2 : ℝ) ^ K) = 3 / (2 : ℝ) ^ K := by field_simp; ring
  rw [hr] at he
  exact he

end Blotto.PRGInput
