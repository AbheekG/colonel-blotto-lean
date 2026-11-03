import Blotto.RoundedProductFieldLearner
import Blotto.RationalSingleFieldLoss
import Blotto.RoundedFiniteGameGap

/-! A concrete finite canonical two-player sparse security trainer. Training
observations are independent whole feasible labels and one value-weighted
field. Each selected stored field is rounded after multiplication. The exact
ideal transition is semantic finite data; native bit-law approximation and
continuous comparator/input compiler contracts remain separate. -/

namespace Blotto
open scoped BigOperators Classical

structure ProductSecurityTrainer (fields : ℕ) where
  sizesA : Fin fields → ℕ
  sizesB : Fin fields → ℕ
  bidsA : (j : Fin fields) → Fin (sizesA j) → ℚ
  bidsB : (j : Fin fields) → Fin (sizesB j) → ℚ
  bidsA_nonnegative : ∀ j code, 0 ≤ bidsA j code
  bidsB_nonnegative : ∀ j code, 0 ≤ bidsB j code
  budgetA : ℚ
  budgetB : ℚ
  fallbackA : SparseMW.ProductCodes sizesA
  fallbackB : SparseMW.ProductCodes sizesB
  fallbackA_feasible : SparseMW.productResource bidsA fallbackA ≤ budgetA
  fallbackB_feasible : SparseMW.productResource bidsB fallbackB ≤ budgetB
  values : RationalFieldSelector fields
  eta : ℚ
  theta : ℚ
  eta_unit : 0 < eta ∧ eta ≤ 1 / 4
  theta_unit : 0 < theta ∧ theta ≤ 1 / 2

namespace ProductSecurityTrainer

def actionsA {m : ℕ} (c : ProductSecurityTrainer m) : ℕ := Fintype.card (SparseMW.FeasibleCodes c.bidsA c.budgetA)
def actionsB {m : ℕ} (c : ProductSecurityTrainer m) : ℕ := Fintype.card (SparseMW.FeasibleCodes c.bidsB c.budgetB)
def observations {m : ℕ} (c : ProductSecurityTrainer m) : ℕ := c.actionsA * (c.actionsB * m)

def observed {m : ℕ} (c : ProductSecurityTrainer m) (x : Fin c.observations) :
    ProductFiniteTraining.Observation c.actionsA c.actionsB m :=
  (ProductFiniteTraining.observationEquiv c.actionsA c.actionsB m).symm x

def selected {m : ℕ} (c : ProductSecurityTrainer m) (_h : List (Fin c.observations))
    (x : Fin c.observations) : Fin m := (c.observed x).2.2

noncomputable def codeA {m : ℕ} (c : ProductSecurityTrainer m) (i : Fin c.actionsA) : SparseMW.ProductCodes c.sizesA :=
  ((SparseMW.feasibleEquiv c.bidsA c.budgetA).symm i).val
noncomputable def codeB {m : ℕ} (c : ProductSecurityTrainer m) (j : Fin c.actionsB) : SparseMW.ProductCodes c.sizesB :=
  ((SparseMW.feasibleEquiv c.bidsB c.budgetB).symm j).val

noncomputable def localLossA {m : ℕ} (c : ProductSecurityTrainer m)
    (h : List (Fin c.observations)) (x : Fin c.observations) (code : Fin (c.sizesA (c.selected h x))) : ℚ :=
  SparseMW.rationalShare (c.bidsB (c.selected h x) (c.codeB (c.observed x).2.1 (c.selected h x)))
    (c.bidsA (c.selected h x) code)

noncomputable def localLossB {m : ℕ} (c : ProductSecurityTrainer m)
    (h : List (Fin c.observations)) (x : Fin c.observations) (code : Fin (c.sizesB (c.selected h x))) : ℚ :=
  SparseMW.rationalShare (c.bidsA (c.selected h x) (c.codeA (c.observed x).1 (c.selected h x)))
    (c.bidsB (c.selected h x) code)

theorem localLossA_unit {m : ℕ} (c : ProductSecurityTrainer m) :
    ∀ h x code, 0 ≤ c.localLossA h x code ∧ c.localLossA h x code ≤ 1 :=
  fun _ _ _ => SparseMW.rationalShare_unit _ _
theorem localLossB_unit {m : ℕ} (c : ProductSecurityTrainer m) :
    ∀ h x code, 0 ≤ c.localLossB h x code ∧ c.localLossB h x code ≤ 1 :=
  fun _ _ _ => SparseMW.rationalShare_unit _ _

noncomputable def fieldsA {m : ℕ} (c : ProductSecurityTrainer m) (h : List (Fin c.observations)) :=
  SparseMW.roundedFieldHistory c.selected c.localLossA c.eta c.theta h
noncomputable def fieldsB {m : ℕ} (c : ProductSecurityTrainer m) (h : List (Fin c.observations)) :=
  SparseMW.roundedFieldHistory c.selected c.localLossB c.eta c.theta h

theorem fieldsA_positive {m : ℕ} (c : ProductSecurityTrainer m) (h : List (Fin c.observations)) :
    ∀ j code, 0 < c.fieldsA h j code :=
  SparseMW.roundedFieldHistory_positive c.selected c.localLossA c.eta c.theta c.eta_unit c.theta_unit c.localLossA_unit h
theorem fieldsB_positive {m : ℕ} (c : ProductSecurityTrainer m) (h : List (Fin c.observations)) :
    ∀ j code, 0 < c.fieldsB h j code :=
  SparseMW.roundedFieldHistory_positive c.selected c.localLossB c.eta c.theta c.eta_unit c.theta_unit c.localLossB_unit h

noncomputable def lawA {m : ℕ} (c : ProductSecurityTrainer m) (h : List (Fin c.observations)) : RationalWholeRowLaw c.actionsA m :=
  SparseMW.gibbsWholeRowLaw c.bidsA c.budgetA c.fallbackA c.fallbackA_feasible (c.fieldsA h) (c.fieldsA_positive h)
noncomputable def lawB {m : ℕ} (c : ProductSecurityTrainer m) (h : List (Fin c.observations)) : RationalWholeRowLaw c.actionsB m :=
  SparseMW.gibbsWholeRowLaw c.bidsB c.budgetB c.fallbackB c.fallbackB_feasible (c.fieldsB h) (c.fieldsB_positive h)

noncomputable def transition {m : ℕ} (c : ProductSecurityTrainer m)
    (h : List (Fin c.observations)) (x : Fin c.observations) : ℝ :=
  (ProductFiniteTraining.indexedProbability (c.lawA h) (c.lawB h) c.values x : ℝ)

theorem transition_nonnegative {m : ℕ} (c : ProductSecurityTrainer m) : ∀ h x, 0 ≤ c.transition h x := by
  intro h x
  unfold transition
  exact_mod_cast ProductFiniteTraining.indexedProbability_nonnegative (c.lawA h) (c.lawB h) c.values x
theorem transition_sum {m : ℕ} (c : ProductSecurityTrainer m) : ∀ h, ∑ x, c.transition h x = 1 := by
  intro h
  unfold transition
  change (∑ x : Fin (c.actionsA * (c.actionsB * m)),
    (ProductFiniteTraining.indexedProbability (c.lawA h) (c.lawB h) c.values x : ℝ)) = 1
  have he := ProductFiniteTraining.indexedProbability_sum (c.lawA h) (c.lawB h) c.values
  exact_mod_cast he

noncomputable def empiricalA {m : ℕ} (c : ProductSecurityTrainer m)
    (h : List (Fin c.observations)) (x : Fin c.observations) (i : Fin c.actionsA) : ℝ :=
  (SparseMW.liftedLocalLoss c.bidsA c.budgetA c.selected c.localLossA h x i : ℝ)
noncomputable def empiricalB {m : ℕ} (c : ProductSecurityTrainer m)
    (h : List (Fin c.observations)) (x : Fin c.observations) (j : Fin c.actionsB) : ℝ :=
  (SparseMW.liftedLocalLoss c.bidsB c.budgetB c.selected c.localLossB h x j : ℝ)

noncomputable def matrix {m : ℕ} (c : ProductSecurityTrainer m) (i : Fin c.actionsA) (j : Fin c.actionsB) : ℝ :=
  payoff c.values.values (fun field => (c.bidsB field (c.codeB j field) : ℝ))
    (fun field => (c.bidsA field (c.codeA i field) : ℝ))

theorem matrix_unit {m : ℕ} (c : ProductSecurityTrainer m) (i : Fin c.actionsA) (j : Fin c.actionsB) :
    0 ≤ c.matrix i j ∧ c.matrix i j ≤ 1 :=
  ⟨payoff_nonneg _ _ _, payoff_le_one _ _ _⟩

theorem empiricalA_opposingLoss {m : ℕ} (c : ProductSecurityTrainer m)
    (h : List (Fin c.observations)) (x : Fin c.observations) (i : Fin c.actionsA) :
    c.empiricalA h x i = ProductFiniteTraining.opposingLossA (c.lawB h)
      ((c.lawA h).realRow i) (c.observed x) := by
  exact SparseMW.rationalShare_real _ _
theorem empiricalB_opposingLoss {m : ℕ} (c : ProductSecurityTrainer m)
    (h : List (Fin c.observations)) (x : Fin c.observations) (j : Fin c.actionsB) :
    c.empiricalB h x j = ProductFiniteTraining.opposingLossB (c.lawA h)
      ((c.lawB h).realRow j) (c.observed x) := by
  exact SparseMW.rationalShare_real _ _

theorem conditionalDirectionA {m : ℕ} (c : ProductSecurityTrainer m) (h : List (Fin c.observations)) (i : Fin c.actionsA) :
    SparseMW.conditionalDirection c.transition c.empiricalA h i =
      FiniteSaddle.RowLoss c.matrix (c.lawB h).realWeight i := by
  unfold SparseMW.conditionalDirection
  simp_rw [c.empiricalA_opposingLoss]
  have he := ProductFiniteTraining.indexed_conditionalOpposingLossA (c.lawA h) (c.lawB h) c.values ((c.lawA h).realRow i)
  dsimp only [transition, observed]
  apply he.trans
  rw [(c.lawB h).purePayoff_eq_sum]
  change 1 - (∑ j, (c.lawB h).realWeight j * payoff c.values.values ((c.lawA h).realRow i) ((c.lawB h).realRow j)) =
    ∑ j, payoff c.values.values ((c.lawB h).realRow j) ((c.lawA h).realRow i) * (c.lawB h).realWeight j
  have hp : ∀ j, payoff c.values.values ((c.lawB h).realRow j) ((c.lawA h).realRow i) =
      1 - payoff c.values.values ((c.lawA h).realRow i) ((c.lawB h).realRow j) := by
    intro j
    have hc := payoff_constant_sum c.values.values ((c.lawA h).realRow i) ((c.lawB h).realRow j)
    linarith
  simp_rw [hp]
  simp only [sub_mul, one_mul, Finset.sum_sub_distrib, (c.lawB h).realWeight_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem conditionalDirectionB {m : ℕ} (c : ProductSecurityTrainer m) (h : List (Fin c.observations)) (j : Fin c.actionsB) :
    SparseMW.conditionalDirection c.transition c.empiricalB h j =
      1 - FiniteSaddle.ColumnPayoff c.matrix (c.lawA h).realWeight j := by
  unfold SparseMW.conditionalDirection
  simp_rw [c.empiricalB_opposingLoss]
  have hLoss : ∀ x, ProductFiniteTraining.opposingLossB (c.lawA h) ((c.lawB h).realRow j) (c.observed x) =
      1 - ProductFiniteTraining.empiricalLossB (c.lawA h) ((c.lawB h).realRow j) (c.observed x) := by
    intro x
    have he := share_constant_sum ((c.lawB h).realRow j (c.observed x).2.2)
      ((c.lawA h).realRow (c.observed x).1 (c.observed x).2.2)
    unfold ProductFiniteTraining.opposingLossB ProductFiniteTraining.empiricalLossB
    linarith
  simp_rw [hLoss, mul_sub, mul_one]
  rw [Finset.sum_sub_distrib, c.transition_sum h]
  have he := ProductFiniteTraining.conditionalLossB (c.lawA h) (c.lawB h) c.values ((c.lawB h).realRow j)
  have hIndexed : (∑ x : Fin c.observations, c.transition h x *
      ProductFiniteTraining.empiricalLossB (c.lawA h) ((c.lawB h).realRow j) (c.observed x)) =
      purePayoff c.values.values ((c.lawB h).realRow j) (c.lawA h).law := by
    change (∑ x : Fin (c.actionsA * (c.actionsB * m)),
      (ProductFiniteTraining.indexedProbability (c.lawA h) (c.lawB h) c.values x : ℝ) *
        ProductFiniteTraining.empiricalLossB (c.lawA h) ((c.lawB h).realRow j)
          ((ProductFiniteTraining.observationEquiv c.actionsA c.actionsB m).symm x)) = _
    rw [← Equiv.sum_comp (ProductFiniteTraining.observationEquiv c.actionsA c.actionsB m)]
    simp only [ProductFiniteTraining.indexedProbability, Equiv.symm_apply_apply]
    exact he
  rw [hIndexed, (c.lawA h).purePayoff_eq_sum]
  rfl

theorem actionsA_positive {m : ℕ} (c : ProductSecurityTrainer m) : 0 < c.actionsA :=
  SparseMW.feasibleCard_positive c.bidsA c.budgetA c.fallbackA c.fallbackA_feasible
theorem actionsB_positive {m : ℕ} (c : ProductSecurityTrainer m) : 0 < c.actionsB :=
  SparseMW.feasibleCard_positive c.bidsB c.budgetB c.fallbackB c.fallbackB_feasible

end ProductSecurityTrainer
end Blotto
