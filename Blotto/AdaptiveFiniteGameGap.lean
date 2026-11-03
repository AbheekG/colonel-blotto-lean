import Blotto.FiniteSaddleGap

/-! Finite adaptive two-learner gap composition. Directions must be proved to
equal the actual finite game's conditional losses; native sample-transition
and continuous-game compiler joins remain separate obligations. -/

namespace Blotto
open scoped BigOperators Classical
namespace FiniteSaddle

def pureComparator {n : ℕ} (chosen : Fin n) : Fin n → ℝ := fun i => if i = chosen then 1 else 0

theorem pureComparator_simplex {n : ℕ} (chosen : Fin n) : pureComparator chosen ∈ SparseMW.simplexComparators n := by
  constructor
  · intro i
    unfold pureComparator
    split_ifs <;> norm_num
  · simp [pureComparator]

noncomputable def historyVectorSum {a n : ℕ} (probability : List (Fin a) → Fin n → ℝ) :
    List (Fin a) → Fin n → ℝ
  | [] => fun _ => 0
  | _x :: past => fun i => historyVectorSum probability past i + probability past i

noncomputable def historyAverage {a n : ℕ} (probability : List (Fin a) → Fin n → ℝ)
    (past : List (Fin a)) : Fin n → ℝ := fun i => historyVectorSum probability past i / past.length

theorem historyVectorSum_total {a n : ℕ} (probability : List (Fin a) → Fin n → ℝ)
    (hs : ∀ h, ∑ i, probability h i = 1) (past : List (Fin a)) :
    (∑ i, historyVectorSum probability past i) = past.length := by
  induction past with
  | nil => simp [historyVectorSum]
  | cons x past ih =>
    simp only [historyVectorSum, Finset.sum_add_distrib, ih, hs, List.length_cons, Nat.cast_add, Nat.cast_one]

theorem historyAverage_nonnegative {a n : ℕ} (probability : List (Fin a) → Fin n → ℝ)
    (hp : ∀ h i, 0 ≤ probability h i) (past : List (Fin a)) : ∀ i, 0 ≤ historyAverage probability past i := by
  have hsum : ∀ i, 0 ≤ historyVectorSum probability past i := by
    induction past with
    | nil => intro i; exact le_rfl
    | cons x past ih => intro i; exact add_nonneg (ih i) (hp past i)
  intro i
  exact div_nonneg (hsum i) (by positivity)

theorem historyAverage_total {a n : ℕ} (probability : List (Fin a) → Fin n → ℝ)
    (hs : ∀ h, ∑ i, probability h i = 1) (past : List (Fin a)) (hlen : 0 < past.length) :
    (∑ i, historyAverage probability past i) = 1 := by
  unfold historyAverage
  simp only [div_eq_mul_inv]
  rw [← Finset.sum_mul, historyVectorSum_total probability hs past]
  exact mul_inv_cancel₀ (by exact_mod_cast Nat.ne_of_gt hlen)

theorem history_gap_identity {a n m : ℕ} (matrix : Fin n → Fin m → ℝ)
    (p : List (Fin a) → Fin n → ℝ) (q : List (Fin a) → Fin m → ℝ)
    (hq : ∀ h, ∑ j, q h j = 1) (past : List (Fin a)) (i : Fin n) (j : Fin m) :
    (past.length : ℝ) * GapAt matrix (historyAverage p past) (historyAverage q past) i j =
      SparseMW.cumulativePairing (fun h _x k => RowLoss matrix (q h) k) p (pureComparator i) past +
        SparseMW.cumulativePairing (fun h _x k => 1 - ColumnPayoff matrix (p h) k) q (pureComparator j) past := by
  have hraw : ColumnPayoff matrix (historyVectorSum p past) j - RowLoss matrix (historyVectorSum q past) i =
      SparseMW.cumulativePairing (fun h _x k => RowLoss matrix (q h) k) p (pureComparator i) past +
        SparseMW.cumulativePairing (fun h _x k => 1 - ColumnPayoff matrix (p h) k) q (pureComparator j) past := by
    induction past with
    | nil => simp [historyVectorSum, ColumnPayoff, RowLoss, SparseMW.cumulativePairing]
    | cons x past ih =>
      simp only [historyVectorSum, ColumnPayoff, RowLoss, add_mul, mul_add, Finset.sum_add_distrib,
        SparseMW.cumulativePairing]
      have hrow : (∑ k, RowLoss matrix (q past) k * (p past k - pureComparator i k)) =
          Bilinear matrix (p past) (q past) - RowLoss matrix (q past) i := by
        unfold pureComparator Bilinear
        simp only [mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero]
        simp
        apply Finset.sum_congr rfl
        intro k _
        ring
      have hcol : (∑ k, (1 - ColumnPayoff matrix (p past) k) * (q past k - pureComparator j k)) =
          ColumnPayoff matrix (p past) j - Bilinear matrix (p past) (q past) := by
        unfold pureComparator
        simp only [mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero]
        simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
        have he : (∑ k, (1 - ColumnPayoff matrix (p past) k) * q past k) =
            1 - Bilinear matrix (p past) (q past) := by
          simp only [sub_mul, one_mul, Finset.sum_sub_distrib, hq past]
          rw [bilinear_columns]
          congr 1
          apply Finset.sum_congr rfl
          intro k _
          ring
        rw [he]
        ring
      dsimp only [RowLoss] at hrow
      dsimp only [ColumnPayoff] at hcol
      rw [hrow, hcol]
      dsimp only [ColumnPayoff, RowLoss] at ih
      linarith
  rw [← hraw]
  unfold GapAt historyAverage ColumnPayoff RowLoss
  simp only [div_eq_mul_inv]
  have hc : (∑ k, (historyVectorSum p past k * (past.length : ℝ)⁻¹) * matrix k j) =
      (∑ k, historyVectorSum p past k * matrix k j) * (past.length : ℝ)⁻¹ := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hr : (∑ k, matrix i k * (historyVectorSum q past k * (past.length : ℝ)⁻¹)) =
      (∑ k, matrix i k * historyVectorSum q past k) * (past.length : ℝ)⁻¹ := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hc, hr]
  cases past with
  | nil => simp [historyVectorSum]
  | cons x past =>
    have hn : ((x :: past).length : ℝ) ≠ 0 := by exact_mod_cast (show (x :: past).length ≠ 0 by simp)
    field_simp [hn]

theorem computed_two_learner_expected_gap {a n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (matrix : Fin n → Fin m → ℝ) (transition : List (Fin a) → Fin a → ℝ)
    (hTransition : ∀ h x, 0 ≤ transition h x) (hTransitionSum : ∀ h, ∑ x, transition h x = 1)
    (rowLoss : List (Fin a) → Fin a → Fin n → ℚ)
    (columnLoss : List (Fin a) → Fin a → Fin m → ℚ) (eta theta : ℚ)
    (heta : 0 < eta ∧ eta ≤ 1 / 4) (htheta : 0 < theta ∧ theta ≤ 1 / 2)
    (hRowUnit : ∀ h x i, 0 ≤ rowLoss h x i ∧ rowLoss h x i ≤ 1)
    (hColumnUnit : ∀ h x j, 0 ≤ columnLoss h x j ∧ columnLoss h x j ≤ 1)
    (hRowDirection : ∀ h i, SparseMW.conditionalDirection transition
        (fun h x i => (rowLoss h x i : ℝ)) h i =
      RowLoss matrix (SparseMW.normalizedReal (SparseMW.rationalHistory
        (SparseMW.computedHistoryMultipliers columnLoss eta theta) h)) i)
    (hColumnDirection : ∀ h j, SparseMW.conditionalDirection transition
        (fun h x j => (columnLoss h x j : ℝ)) h j =
      1 - ColumnPayoff matrix (SparseMW.normalizedReal (SparseMW.rationalHistory
        (SparseMW.computedHistoryMultipliers rowLoss eta theta) h)) j)
    (T : ℕ) :
    let p := fun h => SparseMW.normalizedReal (SparseMW.rationalHistory
      (SparseMW.computedHistoryMultipliers rowLoss eta theta) h)
    let q := fun h => SparseMW.normalizedReal (SparseMW.rationalHistory
      (SparseMW.computedHistoryMultipliers columnLoss eta theta) h)
    (eta : ℝ) * (T : ℝ) * SparseMW.historyMean transition T (fun past =>
      GapAt matrix (historyAverage p past) (historyAverage q past)
        (minimizingRow hn matrix (historyAverage q past))
        (maximizingColumn hm matrix (historyAverage p past))) ≤
      2 * (Real.log n + Real.log m) + (eta : ℝ) ^ 2 * (T : ℝ) *
        ((1 + 2 * (theta : ℝ) / (eta : ℝ)) ^ 2 + 1) + 4 * (theta : ℝ) * T := by
  dsimp only
  let p := fun h => SparseMW.normalizedReal (SparseMW.rationalHistory
    (SparseMW.computedHistoryMultipliers rowLoss eta theta) h)
  let q := fun h => SparseMW.normalizedReal (SparseMW.rationalHistory
    (SparseMW.computedHistoryMultipliers columnLoss eta theta) h)
  let selectedRow := fun past => pureComparator (minimizingRow hn matrix (historyAverage q past))
  let selectedColumn := fun past => pureComparator (maximizingColumn hm matrix (historyAverage p past))
  have hRow := SparseMW.computedHistory_expected_regret hn transition hTransition hTransitionSum
    rowLoss eta theta heta htheta hRowUnit T selectedRow (fun past => pureComparator_simplex _)
  have hColumn := SparseMW.computedHistory_expected_regret hm transition hTransition hTransitionSum
    columnLoss eta theta heta htheta hColumnUnit T selectedColumn (fun past => pureComparator_simplex _)
  simp_rw [hRowDirection] at hRow
  simp_rw [hColumnDirection] at hColumn
  have hqSum : ∀ h, ∑ j, q h j = 1 := by
    intro h
    apply SparseMW.normalizedReal_sum hm
    apply SparseMW.rationalHistory_positive
    intro previous x j
    exact (SparseMW.expMultiplierNative_unit _ _
      ⟨mul_nonneg heta.1.le (hColumnUnit previous x j).1,
        (mul_le_of_le_one_right heta.1.le (hColumnUnit previous x j).2).trans heta.2⟩ htheta).1
  have hmeanIdentity : (T : ℝ) * SparseMW.historyMean transition T (fun past =>
      GapAt matrix (historyAverage p past) (historyAverage q past)
        (minimizingRow hn matrix (historyAverage q past))
        (maximizingColumn hm matrix (historyAverage p past))) =
      SparseMW.historyMean transition T (fun past =>
        SparseMW.cumulativePairing (fun h _x i => RowLoss matrix (q h) i) p (selectedRow past) past) +
      SparseMW.historyMean transition T (fun past =>
        SparseMW.cumulativePairing (fun h _x j => 1 - ColumnPayoff matrix (p h) j) q (selectedColumn past) past) := by
    rw [← SparseMW.historyMean_mul]
    -- Equality is needed only on the supported length-T histories.
    unfold SparseMW.historyMean
    rw [← List.sum_map_add]
    apply congrArg List.sum
    apply List.map_congr_left
    intro past hmem
    have hlen := SparseMW.histories_length past hmem
    dsimp only
    rw [← hlen, history_gap_identity matrix p q hqSum past]
    ring
  have he := add_le_add hRow hColumn
  dsimp only [p, q, selectedRow, selectedColumn] at he hmeanIdentity
  rw [← mul_add] at he
  rw [← hmeanIdentity] at he
  convert he using 1 <;> ring

end FiniteSaddle
end Blotto
