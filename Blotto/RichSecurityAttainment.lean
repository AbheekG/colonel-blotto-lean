import Blotto.RichSmoothingApproximation
import Blotto.CompactFeasibleLaws
import Blotto.ContinuousSecurityValues
import Mathlib.Topology.Semicontinuity.Basic

/-! The poorer player's actual continuous security-loss infimum is attained
for strictly unequal positive budgets with at least two fields. Smoothing
supplies the lower semicontinuous best-response objective; compactness is
over all feasible whole laws. Strong minimax, rich attainment and efficient
selection are separate obligations. -/

namespace Blotto.RichSecurityAttainment
open MeasureTheory Set Filter
open RichSmoothingLaw RichSmoothingApproximation CompactFeasibleLaws ContinuousSecurityValues
open scoped Topology

theorem security_lowerSemicontinuousOn {n : ℕ} (values : Values n) {A B : ℝ}
    (hA : 0 < A) (hn : 2 ≤ n) (hBudgets : B < A) :
    LowerSemicontinuousOn (security values A) {opponent : Mixed n | Supported B opponent} := by
  intro opponent hOpponent threshold hThreshold
  have he : 0 < security values A opponent - threshold := by linarith
  obtain ⟨smooth,hRegular,hBetter⟩ := exists_regular_near_security values hA hn hBudgets
    opponent hOpponent (security values A opponent - threshold) he
  have hGt : threshold < expected values smooth opponent := by linarith
  have hEventual := (regular_rich_expected_continuous values smooth hRegular).continuousAt.tendsto.eventually_const_lt hGt
  apply (hEventual.filter_mono nhdsWithin_le_nhds).mono
  intro other hOther
  exact hOther.trans_le (expected_le_security values smooth other (regular_supported hRegular))

/-- The poor optimal law is a probability law on the original canonical
at-most domain. No finite support, rational weights or rich minimizer is
assumed, and no minimax equality is used. -/
theorem exists_poor_minimizer {n : ℕ} (values : Values n) {A B : ℝ}
    (hB : 0 < B) (hn : 2 ≤ n) (hBudgets : B < A) :
    ∃ opponent : Mixed n, Supported B opponent ∧
      security values A opponent = lossInfimum values B A := by
  have hA : 0 < A := hB.trans hBudgets
  have hNonempty : {opponent : Mixed n | Supported B opponent}.Nonempty :=
    ⟨PureBoundaryEquilibria.pointLaw (fun _ => 0),
      PureBoundaryEquilibria.pointLaw_supported _ _ (feasible_zero hB.le)⟩
  obtain ⟨opponent,hOpponent,hMin⟩ :=
    (security_lowerSemicontinuousOn values hA hn hBudgets).exists_isMinOn
      hNonempty (supported_compact B)
  refine ⟨opponent,hOpponent,le_antisymm ?_ ?_⟩
  · exact le_lossInfimum values B A _ hB.le (fun other hOther => hMin hOther)
  · exact lossInfimum_le_of_supported values B A hA.le opponent hOpponent

end Blotto.RichSecurityAttainment
