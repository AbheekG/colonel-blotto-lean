import Blotto.ProductSecurityTrainer

/-! The concrete exact finite sparse-field trainer has the expected saddle
bound with its actual stored-product rounding. Native bounded sampling,
continuous comparator/compiler transfer and complete complexity remain open. -/

namespace Blotto
open scoped BigOperators Classical
namespace ProductSecurityTrainer

noncomputable def multiplierA {m : ℕ} (c : ProductSecurityTrainer m) :
    List (Fin c.observations) → Fin c.observations → Fin c.actionsA → ℚ :=
  SparseMW.actionHistoryMultiplier c.bidsA c.budgetA c.selected
    (SparseMW.roundedFieldRatio c.selected c.localLossA c.eta c.theta)
noncomputable def multiplierB {m : ℕ} (c : ProductSecurityTrainer m) :
    List (Fin c.observations) → Fin c.observations → Fin c.actionsB → ℚ :=
  SparseMW.actionHistoryMultiplier c.bidsB c.budgetB c.selected
    (SparseMW.roundedFieldRatio c.selected c.localLossB c.eta c.theta)

theorem multiplierA_unit {m : ℕ} (c : ProductSecurityTrainer m) :
    ∀ h x i, 0 < c.multiplierA h x i ∧ c.multiplierA h x i ≤ 1 := by
  intro h x i
  apply SparseMW.storedRatio_unit
  · exact c.fieldsA_positive h _ _
  · exact ⟨mul_nonneg c.eta_unit.1.le (c.localLossA_unit h x _).1,
      (mul_le_of_le_one_right c.eta_unit.1.le (c.localLossA_unit h x _).2).trans c.eta_unit.2⟩
  · exact c.theta_unit

theorem multiplierB_unit {m : ℕ} (c : ProductSecurityTrainer m) :
    ∀ h x i, 0 < c.multiplierB h x i ∧ c.multiplierB h x i ≤ 1 := by
  intro h x i
  apply SparseMW.storedRatio_unit
  · exact c.fieldsB_positive h _ _
  · exact ⟨mul_nonneg c.eta_unit.1.le (c.localLossB_unit h x _).1,
      (mul_le_of_le_one_right c.eta_unit.1.le (c.localLossB_unit h x _).2).trans c.eta_unit.2⟩
  · exact c.theta_unit

theorem empiricalA_unit {m : ℕ} (c : ProductSecurityTrainer m) :
    ∀ h x i, 0 ≤ c.empiricalA h x i ∧ c.empiricalA h x i ≤ 1 := by
  intro h x i
  have he := c.localLossA_unit h x (c.codeA i (c.selected h x))
  change (0 : ℝ) ≤ (c.localLossA h x (c.codeA i (c.selected h x)) : ℝ) ∧
    (c.localLossA h x (c.codeA i (c.selected h x)) : ℝ) ≤ 1
  exact ⟨by exact_mod_cast he.1, by exact_mod_cast he.2⟩

theorem empiricalB_unit {m : ℕ} (c : ProductSecurityTrainer m) :
    ∀ h x j, 0 ≤ c.empiricalB h x j ∧ c.empiricalB h x j ≤ 1 := by
  intro h x j
  have he := c.localLossB_unit h x (c.codeB j (c.selected h x))
  change (0 : ℝ) ≤ (c.localLossB h x (c.codeB j (c.selected h x)) : ℝ) ∧
    (c.localLossB h x (c.codeB j (c.selected h x)) : ℝ) ≤ 1
  exact ⟨by exact_mod_cast he.1, by exact_mod_cast he.2⟩

theorem multiplierA_perturbation {m : ℕ} (c : ProductSecurityTrainer m) : ∀ h x i,
    c.empiricalA h x i ≤ SparseMW.effectiveLoss (c.eta : ℝ) (c.multiplierA h x i : ℝ) ∧
      SparseMW.effectiveLoss (c.eta : ℝ) (c.multiplierA h x i : ℝ) ≤
        c.empiricalA h x i + 3 * (c.theta : ℝ) / (c.eta : ℝ) := by
  intro h x i
  apply SparseMW.storedRatio_effectiveLoss
  · exact c.fieldsA_positive h _ _
  · exact c.eta_unit.1
  · exact ⟨mul_nonneg c.eta_unit.1.le (c.localLossA_unit h x _).1,
      (mul_le_of_le_one_right c.eta_unit.1.le (c.localLossA_unit h x _).2).trans c.eta_unit.2⟩
  · exact c.theta_unit

theorem multiplierB_perturbation {m : ℕ} (c : ProductSecurityTrainer m) : ∀ h x j,
    c.empiricalB h x j ≤ SparseMW.effectiveLoss (c.eta : ℝ) (c.multiplierB h x j : ℝ) ∧
      SparseMW.effectiveLoss (c.eta : ℝ) (c.multiplierB h x j : ℝ) ≤
        c.empiricalB h x j + 3 * (c.theta : ℝ) / (c.eta : ℝ) := by
  intro h x j
  apply SparseMW.storedRatio_effectiveLoss
  · exact c.fieldsB_positive h _ _
  · exact c.eta_unit.1
  · exact ⟨mul_nonneg c.eta_unit.1.le (c.localLossB_unit h x _).1,
      (mul_le_of_le_one_right c.eta_unit.1.le (c.localLossB_unit h x _).2).trans c.eta_unit.2⟩
  · exact c.theta_unit

theorem lawA_dense {m : ℕ} (c : ProductSecurityTrainer m) (h : List (Fin c.observations)) :
    (c.lawA h).realWeight = SparseMW.normalizedReal (SparseMW.rationalHistory c.multiplierA h) := by
  change SparseMW.normalizedReal (SparseMW.feasibleVector c.bidsA c.budgetA (c.fieldsA h)) = _
  unfold fieldsA
  rw [SparseMW.roundedFieldHistory_dense_refinement c.bidsA c.budgetA c.selected c.localLossA
    c.eta c.theta c.eta_unit c.theta_unit c.localLossA_unit]
  rfl

theorem lawB_dense {m : ℕ} (c : ProductSecurityTrainer m) (h : List (Fin c.observations)) :
    (c.lawB h).realWeight = SparseMW.normalizedReal (SparseMW.rationalHistory c.multiplierB h) := by
  change SparseMW.normalizedReal (SparseMW.feasibleVector c.bidsB c.budgetB (c.fieldsB h)) = _
  unfold fieldsB
  rw [SparseMW.roundedFieldHistory_dense_refinement c.bidsB c.budgetB c.selected c.localLossB
    c.eta c.theta c.eta_unit c.theta_unit c.localLossB_unit]
  rfl

theorem expected_gap {m : ℕ} (c : ProductSecurityTrainer m) (T : ℕ) :
    (c.eta : ℝ) * (T : ℝ) * SparseMW.historyMean c.transition T (fun past =>
      FiniteSaddle.GapAt c.matrix (FiniteSaddle.historyAverage (fun h => (c.lawA h).realWeight) past)
        (FiniteSaddle.historyAverage (fun h => (c.lawB h).realWeight) past)
        (FiniteSaddle.minimizingRow c.actionsA_positive c.matrix
          (FiniteSaddle.historyAverage (fun h => (c.lawB h).realWeight) past))
        (FiniteSaddle.maximizingColumn c.actionsB_positive c.matrix
          (FiniteSaddle.historyAverage (fun h => (c.lawA h).realWeight) past))) ≤
      2 * (Real.log c.actionsA + Real.log c.actionsB) + (c.eta : ℝ) ^ 2 * (T : ℝ) *
        ((1 + 3 * (c.theta : ℝ) / (c.eta : ℝ)) ^ 2 + 1) + 6 * (c.theta : ℝ) * T := by
  have he := FiniteSaddle.two_perturbed_learner_expected_gap c.actionsA_positive c.actionsB_positive
    c.matrix c.transition c.transition_nonnegative c.transition_sum c.empiricalA c.empiricalB
    c.multiplierA c.multiplierB (c.eta : ℝ) (3 * (c.theta : ℝ) / (c.eta : ℝ))
    (by exact_mod_cast c.eta_unit.1) c.multiplierA_unit c.multiplierB_unit
    c.multiplierA_perturbation c.multiplierB_perturbation c.empiricalA_unit c.empiricalB_unit
    (fun h i => (c.conditionalDirectionA h i).trans
      (congrArg (fun q => FiniteSaddle.RowLoss c.matrix q i) (c.lawB_dense h)))
    (fun h j => (c.conditionalDirectionB h j).trans
      (congrArg (fun p => 1 - FiniteSaddle.ColumnPayoff c.matrix p j) (c.lawA_dense h))) T
  simp only at he
  have hp : (fun h => SparseMW.normalizedReal (SparseMW.rationalHistory c.multiplierA h)) =
      fun h => (c.lawA h).realWeight := by funext h; exact (c.lawA_dense h).symm
  have hq : (fun h => SparseMW.normalizedReal (SparseMW.rationalHistory c.multiplierB h)) =
      fun h => (c.lawB h).realWeight := by funext h; exact (c.lawB_dense h).symm
  rw [hp, hq] at he
  have hcancel : 2 * (c.eta : ℝ) * T * (3 * (c.theta : ℝ) / (c.eta : ℝ)) = 6 * (c.theta : ℝ) * T := by
    have heta : (c.eta : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt c.eta_unit.1
    field_simp
    ring
  rw [hcancel] at he
  exact he

end ProductSecurityTrainer
end Blotto
