import Blotto.ProductRawSecuritySimulation

/-! Actual rational temporal laws of the sparse security trainer. The rows are
the original feasible code rows, and their weights average the reached Gibbs
laws. The finite response ceiling is derived from these laws; this semantic
certificate does not claim an efficient enumeration of the Cartesian rows. -/

namespace Blotto
open scoped BigOperators Classical
namespace ProductSecurityTrainer

def rationalHistorySum {o r : ℕ} (weight : List (RawObservation o) → Fin r → ℚ) :
    List (RawObservation o) → Fin r → ℚ
  | [] => fun _ => 0
  | _x :: past => fun i => rationalHistorySum weight past i + weight past i

theorem rationalHistorySum_nonnegative {o r : ℕ}
    (weight : List (RawObservation o) → Fin r → ℚ)
    (hWeight : ∀ past i, 0 ≤ weight past i) (past : List (RawObservation o)) :
    ∀ i, 0 ≤ rationalHistorySum weight past i := by
  induction past with
  | nil => intro i; exact le_rfl
  | cons x past ih => intro i; exact add_nonneg (ih i) (hWeight past i)

theorem rationalHistorySum_total {o r : ℕ}
    (weight : List (RawObservation o) → Fin r → ℚ)
    (hWeight : ∀ past, ∑ i, weight past i = 1) (past : List (RawObservation o)) :
    (∑ i, rationalHistorySum weight past i) = past.length := by
  induction past with
  | nil => simp [rationalHistorySum]
  | cons x past ih =>
    simp only [rationalHistorySum, Finset.sum_add_distrib, ih, hWeight,
      List.length_cons, Nat.cast_add, Nat.cast_one]

theorem rationalHistorySum_cast {o r : ℕ}
    (weight : List (RawObservation o) → Fin r → ℚ) (past : List (RawObservation o)) :
    (fun i => (rationalHistorySum weight past i : ℝ)) =
      rawHistoryVectorSum (fun h i => (weight h i : ℝ)) past := by
  induction past with
  | nil => funext i; simp [rationalHistorySum, rawHistoryVectorSum]
  | cons x past ih =>
    funext i
    simp only [rationalHistorySum, rawHistoryVectorSum, Rat.cast_add]
    exact congrArg (fun f => f i) ih |> fun h => congrArg (fun x => x + _) h

noncomputable def temporalLaw {o r m : ℕ}
    (family : List (RawObservation o) → RationalWholeRowLaw r m)
    (rows : Fin r → Fin m → ℚ) (past : List (RawObservation o))
    (hPast : 0 < past.length) : RationalWholeRowLaw r m where
  weight := fun i => rationalHistorySum (fun h => (family h).weight) past i / past.length
  nonnegative := fun i => div_nonneg
    (rationalHistorySum_nonnegative _ (fun h => (family h).nonnegative) past i)
    (Nat.cast_nonneg _)
  sum_one := by
    simp only [div_eq_mul_inv]
    rw [← Finset.sum_mul, rationalHistorySum_total _ (fun h => (family h).sum_one)]
    exact mul_inv_cancel₀ (by exact_mod_cast Nat.ne_of_gt hPast)
  row := rows

theorem temporalLaw_realWeight {o r m : ℕ}
    (family : List (RawObservation o) → RationalWholeRowLaw r m)
    (rows : Fin r → Fin m → ℚ) (past : List (RawObservation o))
    (hPast : 0 < past.length) :
    (temporalLaw family rows past hPast).realWeight =
      rawHistoryAverage (fun h => (family h).realWeight) past := by
  funext i
  change ((rationalHistorySum (fun h => (family h).weight) past i /
    (past.length : ℚ) : ℚ) : ℝ) = _
  rw [Rat.cast_div, Rat.cast_natCast]
  have h := congrArg (fun f => f i) (rationalHistorySum_cast
    (fun h => (family h).weight) past)
  dsimp only at h
  rw [h]
  rfl

noncomputable def averageLawA {m : ℕ} (c : ProductSecurityTrainer m)
    (past : List (RawObservation m)) (hPast : 0 < past.length) :
    RationalWholeRowLaw c.actionsA m :=
  temporalLaw c.rawLawA (fun i j => c.bidsA j (c.codeA i j)) past hPast

noncomputable def averageLawB {m : ℕ} (c : ProductSecurityTrainer m)
    (past : List (RawObservation m)) (hPast : 0 < past.length) :
    RationalWholeRowLaw c.actionsB m :=
  temporalLaw c.rawLawB (fun i j => c.bidsB j (c.codeB i j)) past hPast

theorem averageLawA_realWeight {m : ℕ} (c : ProductSecurityTrainer m)
    (past : List (RawObservation m)) (hPast : 0 < past.length) :
    (c.averageLawA past hPast).realWeight =
      rawHistoryAverage (fun h => (c.rawLawA h).realWeight) past :=
  temporalLaw_realWeight _ _ _ _

theorem averageLawB_realWeight {m : ℕ} (c : ProductSecurityTrainer m)
    (past : List (RawObservation m)) (hPast : 0 < past.length) :
    (c.averageLawB past hPast).realWeight =
      rawHistoryAverage (fun h => (c.rawLawB h).realWeight) past :=
  temporalLaw_realWeight _ _ _ _

theorem averageLawA_rows {m : ℕ} (c : ProductSecurityTrainer m)
    (past : List (RawObservation m)) (hPast : 0 < past.length) (i : Fin c.actionsA) :
    (c.averageLawA past hPast).row i = fun j => c.bidsA j (c.codeA i j) := rfl

theorem averageLawB_rows {m : ℕ} (c : ProductSecurityTrainer m)
    (past : List (RawObservation m)) (hPast : 0 < past.length) (i : Fin c.actionsB) :
    (c.averageLawB past hPast).row i = fun j => c.bidsB j (c.codeB i j) := rfl

theorem averageLawA_row_feasible {m : ℕ} (c : ProductSecurityTrainer m)
    (past : List (RawObservation m)) (hPast : 0 < past.length) (i : Fin c.actionsA) :
    Feasible (c.budgetA : ℝ) ((c.averageLawA past hPast).realRow i) :=
  SparseMW.feasibleRow_hardBudget c.bidsA c.budgetA c.bidsA_nonnegative
    ((SparseMW.feasibleEquiv c.bidsA c.budgetA).symm i)

theorem averageLawB_row_feasible {m : ℕ} (c : ProductSecurityTrainer m)
    (past : List (RawObservation m)) (hPast : 0 < past.length) (i : Fin c.actionsB) :
    Feasible (c.budgetB : ℝ) ((c.averageLawB past hPast).realRow i) :=
  SparseMW.feasibleRow_hardBudget c.bidsB c.budgetB c.bidsB_nonnegative
    ((SparseMW.feasibleEquiv c.bidsB c.budgetB).symm i)

theorem averageLawA_supported {m : ℕ} (c : ProductSecurityTrainer m)
    (past : List (RawObservation m)) (hPast : 0 < past.length) :
    Supported (c.budgetA : ℝ) (c.averageLawA past hPast).law :=
  RationalWholeRowLaw.law_supported _ _ (c.averageLawA_row_feasible past hPast)

theorem averageLawB_supported {m : ℕ} (c : ProductSecurityTrainer m)
    (past : List (RawObservation m)) (hPast : 0 < past.length) :
    Supported (c.budgetB : ℝ) (c.averageLawB past hPast).law :=
  RationalWholeRowLaw.law_supported _ _ (c.averageLawB_row_feasible past hPast)

noncomputable def responseCeiling {m : ℕ} (c : ProductSecurityTrainer m)
    (past : List (RawObservation m)) : ℝ :=
  FiniteSaddle.ColumnPayoff c.matrix (rawHistoryAverage (fun h => (c.rawLawA h).realWeight) past)
    (FiniteSaddle.maximizingColumn c.actionsB_positive c.matrix
      (rawHistoryAverage (fun h => (c.rawLawA h).realWeight) past))

noncomputable def responseFloor {m : ℕ} (c : ProductSecurityTrainer m)
    (past : List (RawObservation m)) : ℝ :=
  FiniteSaddle.RowLoss c.matrix (rawHistoryAverage (fun h => (c.rawLawB h).realWeight) past)
    (FiniteSaddle.minimizingRow c.actionsA_positive c.matrix
      (rawHistoryAverage (fun h => (c.rawLawB h).realWeight) past))

theorem responseCeiling_eq_floor_gap {m : ℕ} (c : ProductSecurityTrainer m)
    (past : List (RawObservation m)) :
    c.responseCeiling past = c.responseFloor past + c.rawGap past := by
  unfold responseCeiling responseFloor rawGap FiniteSaddle.GapAt
  ring

theorem averageLawA_response_payoff {m : ℕ} (c : ProductSecurityTrainer m)
    (past : List (RawObservation m)) (hPast : 0 < past.length) (j : Fin c.actionsB) :
    purePayoff c.values.values (fun field => (c.bidsB field (c.codeB j field) : ℝ))
      (c.averageLawA past hPast).law =
        FiniteSaddle.ColumnPayoff c.matrix
          (rawHistoryAverage (fun h => (c.rawLawA h).realWeight) past) j := by
  rw [RationalWholeRowLaw.purePayoff_eq_sum]
  simp only [averageLawA_realWeight]
  apply Finset.sum_congr rfl
  intro i _
  rfl

/-- The bound covers every feasible dependent code, including duplicate decoded
rows. No finite-payoff bound is supplied to this certificate. -/
theorem averageLawA_finite_response_bound {m : ℕ} (c : ProductSecurityTrainer m)
    (past : List (RawObservation m)) (hPast : 0 < past.length)
    (code : SparseMW.ProductCodes c.sizesB)
    (hCode : SparseMW.productResource c.bidsB code ≤ c.budgetB) :
    purePayoff c.values.values (fun field => (c.bidsB field (code field) : ℝ))
      (c.averageLawA past hPast).law ≤ c.responseCeiling past := by
  let label : Fin c.actionsB := (SparseMW.feasibleEquiv c.bidsB c.budgetB) ⟨code, hCode⟩
  have hLabel : c.codeB label = code := by
    change ((SparseMW.feasibleEquiv c.bidsB c.budgetB).symm
      ((SparseMW.feasibleEquiv c.bidsB c.budgetB) ⟨code, hCode⟩)).val = code
    rw [Equiv.symm_apply_apply]
  rw [← hLabel, c.averageLawA_response_payoff past hPast]
  exact FiniteSaddle.column_le_maximizingColumn _ _ _ label

end ProductSecurityTrainer
end Blotto
