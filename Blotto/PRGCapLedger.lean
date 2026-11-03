import Blotto.PRGDyadicApproximation

/-! The midpoint stage and a supplied capped-branch perturbation compose
to the PRG finite-bit error ledger. The cap-distance and feasibility hypotheses
are explicit: the rational-coin interpreter must still establish them. -/

namespace Blotto.PRGInput

theorem capped_CDF_errors {n : ℕ} (i : PRGInput n) (K : ℕ) (μ ν : Mixed n)
    (hμ : CDFClose μ (i.richDyadicLaw K) (1 / (2 : ℝ) ^ K))
    (hν : CDFClose ν (i.poorDyadicLaw K) (1 / (2 : ℝ) ^ K)) :
    CDFClose i.richLaw μ (5 / (2 * (2 : ℝ) ^ K)) ∧
      CDFClose i.poorLaw ν (5 / (2 * (2 : ℝ) ^ K)) := by
  have hA := hμ.triangle (i.richDyadicLaw_CDF_error K)
  have hB := hν.triangle (i.poorDyadicLaw_CDF_error K)
  have hr : 1 / (2 : ℝ) ^ K + 3 / (2 * (2 : ℝ) ^ K) = 5 / (2 * (2 : ℝ) ^ K) := by field_simp; ring
  rw [hr] at hA hB
  exact ⟨hA.symm, hB.symm⟩

theorem capped_regrets {n : ℕ} (i : PRGInput n) (K : ℕ) (μ ν : Mixed n)
    (hsμ : Supported 1 μ) (hsν : Supported i.b ν)
    (hμ : CDFClose μ (i.richDyadicLaw K) (1 / (2 : ℝ) ^ K))
    (hν : CDFClose ν (i.poorDyadicLaw K) (1 / (2 : ℝ) ^ K)) :
    regret i.values 1 μ ν ≤ 5 / (2 : ℝ) ^ K ∧ regret i.values i.b ν μ ≤ 5 / (2 : ℝ) ^ K := by
  have hc := i.capped_CDF_errors K μ ν hμ hν
  have he := i.approximation_regrets μ ν hsμ hsν hc.1 hc.2
  have hr : 5 / (2 * (2 : ℝ) ^ K) + 5 / (2 * (2 : ℝ) ^ K) = 5 / (2 : ℝ) ^ K := by field_simp; ring
  rw [hr] at he
  exact he

theorem capped_epsilon {n : ℕ} (i : PRGInput n) {ε : ℝ} (hε : 0 < ε) {K : ℕ}
    (hK : 32 ≤ ε * (2 : ℝ) ^ K) (μ ν : Mixed n) (hsμ : Supported 1 μ) (hsν : Supported i.b ν)
    (hμ : CDFClose μ (i.richDyadicLaw K) (1 / (2 : ℝ) ^ K))
    (hν : CDFClose ν (i.poorDyadicLaw K) (1 / (2 : ℝ) ^ K)) :
    regret i.values 1 μ ν < ε ∧ regret i.values i.b ν μ < ε := by
  have hc := i.capped_CDF_errors K μ ν hμ hν
  exact prg_epsilon_of_distances i hε hK μ ν hsμ hsν hc.1 hc.2

end Blotto.PRGInput
