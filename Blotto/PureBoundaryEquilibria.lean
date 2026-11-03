import Blotto.ProductSamplerProbability

/-! The retained one-field and equal-budget dominant-field boundaries used
by the general D1 algorithms. Both are exact independent degenerate laws in
the canonical at-most game, including every zero tie. These elementary
branches carry no novelty claim. Runtime/encoded-output selectors are separate
from the mathematical boundary contracts proved here. -/

namespace Blotto.PureBoundaryEquilibria
open MeasureTheory
open scoped BigOperators Classical

noncomputable def vertex {n : ℕ} (budget : ℝ) (chosen : Fin n) : Allocation n :=
  fun j => if j = chosen then budget else 0

theorem vertex_fullBudget {n : ℕ} (budget : ℝ) (hB : 0 ≤ budget) (chosen : Fin n) :
    FullBudget budget (vertex budget chosen) := by
  constructor
  · intro j; unfold vertex; split_ifs
    · exact hB
    · exact le_rfl
  · simp [vertex]

theorem feasible_coordinate_le {n : ℕ} {budget : ℝ} {row : Allocation n}
    (hRow : Feasible budget row) (j : Fin n) : row j ≤ budget :=
  (Finset.single_le_sum (fun k _ => hRow.1 k) (Finset.mem_univ j)).trans hRow.2

theorem feasible_at_budget_eq_vertex {n : ℕ} {budget : ℝ} {row : Allocation n}
    (hRow : Feasible budget row) (chosen : Fin n) (hChosen : row chosen = budget) :
    row = vertex budget chosen := by
  have hSum := Finset.sum_erase_add Finset.univ row (Finset.mem_univ chosen)
  have hRest : (∑ j ∈ Finset.univ.erase chosen, row j) ≤ 0 := by
    rw [hChosen] at hSum
    linarith [hRow.2]
  funext j
  by_cases h : j = chosen
  · subst j; simp [vertex, hChosen]
  · have hMember : j ∈ Finset.univ.erase chosen := Finset.mem_erase.mpr ⟨h, Finset.mem_univ j⟩
    have hUpper : row j ≤ 0 :=
      (Finset.single_le_sum (fun k _ => hRow.1 k) hMember).trans hRest
    simp only [vertex, h, ite_false]
    exact le_antisymm hUpper (hRow.1 j)

theorem self_payoff {n : ℕ} (values : Values n) (row : Allocation n) :
    payoff values row row = 1 / 2 := by
  unfold payoff
  simp only [share_tie]
  rw [← Finset.sum_mul, values.normalized]
  norm_num

theorem dominant_vertex_response {n : ℕ} (values : Values n) (budget : ℝ)
    (chosen : Fin n) (hHeavy : 1 / 2 ≤ values.weight chosen)
    (row : Allocation n) (hRow : Feasible budget row) :
    payoff values row (vertex budget chosen) ≤ 1 / 2 := by
  have hChosen := feasible_coordinate_le hRow chosen
  by_cases hEqual : row chosen = budget
  · rw [feasible_at_budget_eq_vertex hRow chosen hEqual, self_payoff]
  · have hStrict : row chosen < budget := lt_of_le_of_ne hChosen hEqual
    have hShare : share (row chosen) budget = 0 := by
      simp [share, not_lt_of_ge hStrict.le, hEqual]
    calc
      payoff values row (vertex budget chosen) =
          ∑ j ∈ Finset.univ.erase chosen,
            values.weight j * share (row j) (vertex budget chosen j) := by
        rw [payoff, ← Finset.sum_erase_add Finset.univ
          (fun j => values.weight j * share (row j) (vertex budget chosen j)) (Finset.mem_univ chosen)]
        simp only [vertex, ite_true, hShare, mul_zero, add_zero]
      _ ≤ ∑ j ∈ Finset.univ.erase chosen, values.weight j :=
        Finset.sum_le_sum fun j _ => mul_le_of_le_one_right
          (values.positive j).le (share_le_one _ _)
      _ = 1 - values.weight chosen := by
        have h := Finset.sum_erase_add Finset.univ values.weight (Finset.mem_univ chosen)
        rw [values.normalized] at h
        linarith
      _ ≤ 1 / 2 := by linarith

noncomputable def pointLaw {n : ℕ} (row : Allocation n) : Mixed n :=
  ProductBidTree.allocationPointLaw row

theorem purePayoff_pointLaw {n : ℕ} (values : Values n) (row opponent : Allocation n) :
    purePayoff values row (pointLaw opponent) = payoff values row opponent := by
  change (∫ y, payoff values row y ∂Measure.dirac opponent) = _
  rw [integral_dirac]

theorem expected_pointLaw {n : ℕ} (values : Values n) (row opponent : Allocation n) :
    expected values (pointLaw row) (pointLaw opponent) = payoff values row opponent := by
  rw [expected_iterated]
  simp_rw [purePayoff_pointLaw]
  change (∫ x, payoff values x opponent ∂Measure.dirac row) = _
  rw [integral_dirac]

theorem pointLaw_supported {n : ℕ} (budget : ℝ) (row : Allocation n)
    (hRow : Feasible budget row) : Supported budget (pointLaw row) := by
  change ∀ᵐ x ∂Measure.dirac row, Feasible budget x
  rw [ae_dirac_eq]
  exact hRow

theorem dominant_vertex_security {n : ℕ} (values : Values n) (budget : ℝ)
    (hB : 0 ≤ budget) (chosen : Fin n) (hHeavy : 1 / 2 ≤ values.weight chosen) :
    security values budget (pointLaw (vertex budget chosen)) = 1 / 2 := by
  apply le_antisymm
  · apply security_le values hB
    intro row hRow
    rw [purePayoff_pointLaw]
    exact dominant_vertex_response values budget chosen hHeavy row hRow
  · have h := purePayoff_le_security values
      (fullBudget_feasible (vertex_fullBudget budget hB chosen)) (pointLaw (vertex budget chosen))
    rw [purePayoff_pointLaw, self_payoff] at h
    exact h

theorem dominant_vertex_equilibrium {n : ℕ} (values : Values n) (budget : ℝ)
    (hB : 0 ≤ budget) (chosen : Fin n) (hHeavy : 1 / 2 ≤ values.weight chosen) :
    Supported budget (pointLaw (vertex budget chosen)) ∧
      regret values budget (pointLaw (vertex budget chosen)) (pointLaw (vertex budget chosen)) = 0 := by
  refine ⟨pointLaw_supported budget _ (fullBudget_feasible (vertex_fullBudget budget hB chosen)), ?_⟩
  rw [regret, dominant_vertex_security values budget hB chosen hHeavy,
    expected_pointLaw, self_payoff]
  ring

noncomputable def oneFieldRow (budget : ℝ) : Allocation 1 := fun _ => budget

theorem oneFieldRow_fullBudget (budget : ℝ) (hB : 0 ≤ budget) :
    FullBudget budget (oneFieldRow budget) := by
  exact ⟨fun _ => hB, by simp [oneFieldRow]⟩

theorem oneField_security (values : Values 1) (budget opponentBudget : ℝ) (hB : 0 ≤ budget) :
    security values budget (pointLaw (oneFieldRow opponentBudget)) =
      payoff values (oneFieldRow budget) (oneFieldRow opponentBudget) := by
  apply le_antisymm
  · apply security_le values hB
    intro row hRow
    rw [purePayoff_pointLaw]
    exact payoff_mono_bid values (fun j => feasible_coordinate_le hRow j) _
  · have h := purePayoff_le_security values
      (fullBudget_feasible (oneFieldRow_fullBudget budget hB)) (pointLaw (oneFieldRow opponentBudget))
    rw [purePayoff_pointLaw] at h
    exact h

theorem oneField_equilibrium (values : Values 1) (richBudget poorBudget : ℝ)
    (hRich : 0 ≤ richBudget) (hPoor : 0 ≤ poorBudget) :
    Supported richBudget (pointLaw (oneFieldRow richBudget)) ∧
      Supported poorBudget (pointLaw (oneFieldRow poorBudget)) ∧
      regret values richBudget (pointLaw (oneFieldRow richBudget)) (pointLaw (oneFieldRow poorBudget)) = 0 ∧
      regret values poorBudget (pointLaw (oneFieldRow poorBudget)) (pointLaw (oneFieldRow richBudget)) = 0 := by
  refine ⟨pointLaw_supported _ _ (fullBudget_feasible (oneFieldRow_fullBudget _ hRich)),
    pointLaw_supported _ _ (fullBudget_feasible (oneFieldRow_fullBudget _ hPoor)), ?_, ?_⟩
  · rw [regret, oneField_security values _ _ hRich, expected_pointLaw]; ring
  · rw [regret, oneField_security values _ _ hPoor, expected_pointLaw]; ring

end Blotto.PureBoundaryEquilibria
