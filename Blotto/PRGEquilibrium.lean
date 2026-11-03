import Blotto.LottoResourceSystem

/-! Exact PRG common-value equilibrium in normalized budgets 1 and b.
The laws below are constructed from resource rounding, greedy grouping, and
the explicit small-dimensional couplings. Sampler/cost and finite-bit
implementation claims are not implied by this mathematical-law theorem. -/

namespace Blotto
open MeasureTheory
open scoped BigOperators

structure PRGInput (n : ℕ) where
  values : Values n
  b : ℝ
  b_pos : 0 < b
  b_le : b ≤ 1
  small_fields : ∀ j, 2 * values.weight j ≤ b

namespace PRGInput

noncomputable def richSystem {n : ℕ} (i : PRGInput n) : LottoResourceSystem n where
  B := 1
  length := fun j => 2 * i.values.weight j
  initial := fun j => 2 * i.values.weight j
  B_pos := by norm_num
  length_pos := fun j => mul_pos (by norm_num) (i.values.positive j)
  length_le := fun j => (i.small_fields j).trans i.b_le
  initial_box := fun j => ⟨le_of_lt (mul_pos (by norm_num) (i.values.positive j)), le_rfl⟩
  initial_sum := by rw [← Finset.mul_sum, i.values.normalized]

noncomputable def poorSystem {n : ℕ} (i : PRGInput n) : LottoResourceSystem n where
  B := i.b
  length := fun j => 2 * i.values.weight j
  initial := fun j => i.b * (2 * i.values.weight j)
  B_pos := i.b_pos
  length_pos := fun j => mul_pos (by norm_num) (i.values.positive j)
  length_le := i.small_fields
  initial_box := fun j => ⟨le_of_lt (mul_pos i.b_pos (mul_pos (by norm_num) (i.values.positive j))), by
    have h := mul_le_mul_of_nonneg_right i.b_le
      (le_of_lt (mul_pos (by norm_num : (0 : ℝ) < 2) (i.values.positive j)))
    simpa only [one_mul] using h⟩
  initial_sum := by rw [← Finset.mul_sum, ← Finset.mul_sum, i.values.normalized]; ring

noncomputable def richLaw {n : ℕ} (i : PRGInput n) : Mixed n := i.richSystem.law
noncomputable def poorLaw {n : ℕ} (i : PRGInput n) : Mixed n := i.poorSystem.law

theorem richLaw_fullBudget {n : ℕ} (i : PRGInput n) :
    ∀ᵐ x ∂(i.richLaw : Measure (Allocation n)), FullBudget 1 x := i.richSystem.law_contract.1

theorem poorLaw_fullBudget {n : ℕ} (i : PRGInput n) :
    ∀ᵐ x ∂(i.poorLaw : Measure (Allocation n)), FullBudget i.b x := i.poorSystem.law_contract.1

theorem richLaw_marginal {n : ℕ} (i : PRGInput n) (j : Fin n) :
    (marginal i.richLaw j : Measure ℝ) = uniformLaw (2 * i.values.weight j) := by
  rw [richLaw, i.richSystem.law_contract.2 j]
  change affineMeasure ((2 * i.values.weight j) / (2 * i.values.weight j))
    (uniformLaw (2 * i.values.weight j)) (Measure.dirac 0) = _
  rw [div_self (ne_of_gt (mul_pos (by norm_num) (i.values.positive j)))]
  simp [affineMeasure]

theorem poorLaw_marginal {n : ℕ} (i : PRGInput n) (j : Fin n) :
    (marginal i.poorLaw j : Measure ℝ) = zeroUniformLaw (2 * i.values.weight j) i.b := by
  rw [poorLaw, i.poorSystem.law_zeroUniform j]
  change zeroUniformLaw (2 * i.values.weight j)
    ((i.b * (2 * i.values.weight j)) / (2 * i.values.weight j)) = _
  rw [mul_div_cancel_right₀ _ (ne_of_gt (mul_pos (by norm_num) (i.values.positive j)))]

theorem equilibrium {n : ℕ} (i : PRGInput n) :
    regret i.values 1 i.richLaw i.poorLaw = 0 ∧
      regret i.values i.b i.poorLaw i.richLaw = 0 ∧
      expected i.values i.richLaw i.poorLaw = 1 - i.b / 2 ∧
      expected i.values i.poorLaw i.richLaw = i.b / 2 :=
  feasible_lotto_couplings_equilibrium i.values i.b_pos i.b_le _ _
    i.richSystem.law_supported i.poorSystem.law_supported
    i.richLaw_marginal i.poorLaw_marginal

end PRGInput

theorem exists_prg_equilibrium {n : ℕ} (v : Values n) {b : ℝ}
    (hb : 0 < b) (hb1 : b ≤ 1) (hfield : ∀ j, v.weight j ≤ b / 2) :
    ∃ μ ν : Mixed n, Supported 1 μ ∧ Supported b ν ∧
      (∀ j, (marginal μ j : Measure ℝ) = uniformLaw (2 * v.weight j)) ∧
      (∀ j, (marginal ν j : Measure ℝ) = zeroUniformLaw (2 * v.weight j) b) ∧
      regret v 1 μ ν = 0 ∧ regret v b ν μ = 0 ∧
      expected v μ ν = 1 - b / 2 ∧ expected v ν μ = b / 2 := by
  let i : PRGInput n := ⟨v, b, hb, hb1, fun j => by linarith [hfield j]⟩
  exact ⟨i.richLaw, i.poorLaw, i.richSystem.law_supported, i.poorSystem.law_supported,
    i.richLaw_marginal, i.poorLaw_marginal, i.equilibrium⟩

end Blotto
