import Blotto.RichMinimaxCover

/-! Retained R33 strong minimax for strictly unequal positive budgets.
The actual two continuous security-loss infima sum to one, and independent
near-optimal whole laws have both continuous Nash guarantees. Rich attainment
and efficient construction are not inferred from this existence proof. -/

namespace Blotto.RichMinimax
open MeasureTheory Set
open RichSmoothingLaw RichMinimaxCover ContinuousSecurityValues

theorem expected_pointLaw_left {n : ℕ} (values : Values n) (row : Allocation n) (law : Mixed n) :
    expected values (PureBoundaryEquilibria.pointLaw row) law = purePayoff values row law := by
  rw [expected_iterated]
  change (∫ x, purePayoff values x law ∂Measure.dirac row) = _
  rw [integral_dirac]

theorem exists_regular_security_bound {n : ℕ} (values : Values n) {A B : ℝ}
    (hB : 0 < B) (hn : 2 ≤ n) (hBudgets : B < A) (threshold : ℝ)
    (hThreshold : threshold < lossInfimum values B A) :
    ∃ smooth : Mixed n, Regular A smooth ∧ security values B smooth ≤ 1 - threshold := by
  obtain ⟨smooth,hRegular,hUniform⟩ := exists_regular_uniform_response values hB hn hBudgets threshold hThreshold
  refine ⟨smooth,hRegular,security_le values hB.le smooth ?_⟩
  intro row hRow
  have hBetter := hUniform (PureBoundaryEquilibria.pointLaw row)
    (PureBoundaryEquilibria.pointLaw_supported B row hRow)
  have hSum := expected_constant_sum values smooth (PureBoundaryEquilibria.pointLaw row)
  rw [expected_pointLaw_left] at hSum
  linarith

/-- The reverse weak-duality inequality is derived by regular-rich finite
cover/separation. Both infima range over the original hard at-most domain. -/
theorem lossInfimum_sum_le_one {n : ℕ} (values : Values n) {A B : ℝ}
    (hB : 0 < B) (hn : 2 ≤ n) (hBudgets : B < A) :
    lossInfimum values A B + lossInfimum values B A ≤ 1 := by
  by_contra hFail
  let gap := lossInfimum values A B + lossInfimum values B A - 1
  have hGap : 0 < gap := by dsimp [gap]; linarith
  let threshold := lossInfimum values B A - gap / 2
  have hThreshold : threshold < lossInfimum values B A := by dsimp [threshold]; linarith
  obtain ⟨smooth,hRegular,hSecurity⟩ := exists_regular_security_bound values hB hn hBudgets threshold hThreshold
  have hInfimum := lossInfimum_le_of_supported values A B hB.le smooth (regular_supported hRegular)
  dsimp [threshold,gap] at hSecurity
  linarith

theorem lossInfimum_sum_eq_one {n : ℕ} (values : Values n) {A B : ℝ}
    (hB : 0 < B) (hn : 2 ≤ n) (hBudgets : B < A) :
    lossInfimum values A B + lossInfimum values B A = 1 :=
  le_antisymm (lossInfimum_sum_le_one values hB hn hBudgets)
    (lossInfimum_sum_ge_one values A B (hB.trans hBudgets).le hB.le)

/-- Abstract existence of independent near-optimal canonical whole laws.
This supplies no efficient compiler, finite-output selector or runtime. -/
theorem exists_approximate_equilibrium {n : ℕ} (values : Values n) {A B : ℝ}
    (hB : 0 < B) (hn : 2 ≤ n) (hBudgets : B < A) (epsilon : ℝ) (he : 0 < epsilon) :
    ∃ rich poor : Mixed n, Supported A rich ∧ Supported B poor ∧
      regret values A rich poor ≤ epsilon ∧ regret values B poor rich ≤ epsilon := by
  obtain ⟨rich,hRich,hRichSecurity⟩ := exists_near_optimal values A B
    (hB.trans hBudgets).le hB.le (epsilon / 2) (by linarith)
  obtain ⟨poor,hPoor,hPoorSecurity⟩ := exists_near_optimal values B A
    hB.le (hB.trans hBudgets).le (epsilon / 2) (by linarith)
  have hValue := lossInfimum_sum_eq_one values hB hn hBudgets
  have hSum : security values A poor + security values B rich ≤ 1 + epsilon := by linarith
  exact ⟨rich,poor,hRich,hPoor,regrets_le_of_security_sum values rich poor hRich hPoor hSum⟩

end Blotto.RichMinimax
