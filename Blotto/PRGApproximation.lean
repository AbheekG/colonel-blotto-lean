import Blotto.PRGEquilibrium

/-! The PRG finite-bit error ledger, conditional on feasible approximation
laws with the stated marginal distances. Midpoint/coin implementations and
their distances must still be proved; no approximation laws are postulated. -/

namespace Blotto
open scoped BigOperators

namespace PRGInput

theorem approximation_regrets {n : ℕ} (i : PRGInput n) (μ ν : Mixed n) {δA δB : ℝ}
    (hμ : Supported 1 μ) (hν : Supported i.b ν)
    (hcμ : CDFClose i.richLaw μ δA) (hcν : CDFClose i.poorLaw ν δB) :
    regret i.values 1 μ ν ≤ δA + δB ∧ regret i.values i.b ν μ ≤ δA + δB := by
  have hsA := abs_le.mp (security_close i.values (by norm_num : (0 : ℝ) ≤ 1) hcν)
  have hsB := abs_le.mp (security_close i.values (le_of_lt i.b_pos) hcμ)
  have hiA := zeroUniform_security i.values (le_of_lt i.b_pos) i.b_le i.poorLaw i.poorLaw_marginal
  have hiB := uniform_security i.values (le_of_lt i.b_pos) i.richLaw i.richLaw_marginal
  apply regrets_le_of_security_sum i.values μ ν hμ hν
  linarith

end PRGInput

theorem prg_branch_cap_algebra (choices precision : ℕ) :
    (2 : ℝ) ^ choices * (3 / 4 : ℝ) ^ (3 * (choices + precision)) ≤ (1 / 2 : ℝ) ^ precision := by
  have he : (2 : ℝ) ^ choices * (3 / 4 : ℝ) ^ (3 * (choices + precision)) =
      (2 * (3 / 4 : ℝ) ^ 3) ^ choices * ((3 / 4 : ℝ) ^ 3) ^ precision := by
    rw [Nat.mul_add, pow_add]
    simp only [mul_pow, ← pow_mul]
    ring
  rw [he]
  have hc : (2 * (3 / 4 : ℝ) ^ 3) ^ choices ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3 / 4) ^ 3)
    (by norm_num : (3 / 4 : ℝ) ^ 3 ≤ 1 / 2) precision
  calc
    _ ≤ 1 * ((3 / 4 : ℝ) ^ 3) ^ precision :=
      mul_le_mul_of_nonneg_right hc (pow_nonneg (by norm_num) _)
    _ ≤ (1 / 2 : ℝ) ^ precision := by simpa only [one_mul] using hp

theorem prg_total_bit_cap (n precision : ℕ) :
    3 * (n + 1000 + precision) + 2 * precision = 3 * n + 3000 + 5 * precision := by omega

theorem prg_precision_error {ε : ℝ} (_hε : 0 < ε) {precision : ℕ}
    (hprecision : 32 ≤ ε * (2 : ℝ) ^ precision) :
    2 * (5 / (2 * (2 : ℝ) ^ precision)) < ε := by
  have hp : (0 : ℝ) < 2 ^ precision := pow_pos (by norm_num) _
  have he : 2 * (5 / (2 * (2 : ℝ) ^ precision)) = 5 / (2 : ℝ) ^ precision := by
    field_simp
  rw [he]
  apply (div_lt_iff₀ hp).mpr
  linarith

theorem prg_epsilon_of_distances {n : ℕ} (i : PRGInput n) {ε : ℝ} (hε : 0 < ε)
    {precision : ℕ} (hprecision : 32 ≤ ε * (2 : ℝ) ^ precision) (μ ν : Mixed n)
    (hμ : Supported 1 μ) (hν : Supported i.b ν)
    (hcμ : CDFClose i.richLaw μ (5 / (2 * (2 : ℝ) ^ precision)))
    (hcν : CDFClose i.poorLaw ν (5 / (2 * (2 : ℝ) ^ precision))) :
    regret i.values 1 μ ν < ε ∧ regret i.values i.b ν μ < ε := by
  have hr := i.approximation_regrets μ ν hμ hν hcμ hcν
  have he := prg_precision_error hε hprecision
  constructor <;> linarith [hr.1, hr.2]

end Blotto
