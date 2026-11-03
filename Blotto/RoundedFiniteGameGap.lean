import Blotto.AdaptiveFiniteGameGap
import Blotto.AdaptivePerturbedRegret

/-! Two-learner saddle composition accepts history-dependent stored ratios.
Every multiplier positivity/unit/perturbation and native conditional-direction
contract remains explicit; stored field histories derive the former separately. -/

namespace Blotto
open scoped BigOperators Classical
namespace FiniteSaddle

theorem two_perturbed_learner_expected_gap {a n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (matrix : Fin n → Fin m → ℝ) (transition : List (Fin a) → Fin a → ℝ)
    (hTransition : ∀ h x, 0 ≤ transition h x) (hTransitionSum : ∀ h, ∑ x, transition h x = 1)
    (rowLoss : List (Fin a) → Fin a → Fin n → ℝ)
    (columnLoss : List (Fin a) → Fin a → Fin m → ℝ)
    (rowMultiplier : List (Fin a) → Fin a → Fin n → ℚ)
    (columnMultiplier : List (Fin a) → Fin a → Fin m → ℚ) (eta error : ℝ) (heta : 0 < eta)
    (hRowMultiplier : ∀ h x i, 0 < rowMultiplier h x i ∧ rowMultiplier h x i ≤ 1)
    (hColumnMultiplier : ∀ h x j, 0 < columnMultiplier h x j ∧ columnMultiplier h x j ≤ 1)
    (hRowPerturb : ∀ h x i, rowLoss h x i ≤ SparseMW.effectiveLoss eta (rowMultiplier h x i : ℝ) ∧
      SparseMW.effectiveLoss eta (rowMultiplier h x i : ℝ) ≤ rowLoss h x i + error)
    (hColumnPerturb : ∀ h x j, columnLoss h x j ≤ SparseMW.effectiveLoss eta (columnMultiplier h x j : ℝ) ∧
      SparseMW.effectiveLoss eta (columnMultiplier h x j : ℝ) ≤ columnLoss h x j + error)
    (hRowUnit : ∀ h x i, 0 ≤ rowLoss h x i ∧ rowLoss h x i ≤ 1)
    (hColumnUnit : ∀ h x j, 0 ≤ columnLoss h x j ∧ columnLoss h x j ≤ 1)
    (hRowDirection : ∀ h i, SparseMW.conditionalDirection transition
        rowLoss h i =
      RowLoss matrix (SparseMW.normalizedReal (SparseMW.rationalHistory
        columnMultiplier h)) i)
    (hColumnDirection : ∀ h j, SparseMW.conditionalDirection transition
        columnLoss h j =
      1 - ColumnPayoff matrix (SparseMW.normalizedReal (SparseMW.rationalHistory
        rowMultiplier h)) j)
    (T : ℕ) :
    let p := fun h => SparseMW.normalizedReal (SparseMW.rationalHistory
      rowMultiplier h)
    let q := fun h => SparseMW.normalizedReal (SparseMW.rationalHistory
      columnMultiplier h)
    eta * (T : ℝ) * SparseMW.historyMean transition T (fun past =>
      GapAt matrix (historyAverage p past) (historyAverage q past)
        (minimizingRow hn matrix (historyAverage q past))
        (maximizingColumn hm matrix (historyAverage p past))) ≤
      2 * (Real.log n + Real.log m) + eta ^ 2 * (T : ℝ) *
        ((1 + error) ^ 2 + 1) + 2 * eta * T * error := by
  dsimp only
  let p := fun h => SparseMW.normalizedReal (SparseMW.rationalHistory
    rowMultiplier h)
  let q := fun h => SparseMW.normalizedReal (SparseMW.rationalHistory
    columnMultiplier h)
  let selectedRow := fun past => pureComparator (minimizingRow hn matrix (historyAverage q past))
  let selectedColumn := fun past => pureComparator (maximizingColumn hm matrix (historyAverage p past))
  have hRow := SparseMW.rationalHistory_expected_original_regret hn transition hTransition hTransitionSum
    rowMultiplier rowLoss eta error heta (fun h x i => (hRowMultiplier h x i).1)
    (fun h x i => (hRowMultiplier h x i).2) hRowUnit hRowPerturb T selectedRow (fun past => pureComparator_simplex _)
  have hColumn := SparseMW.rationalHistory_expected_original_regret hm transition hTransition hTransitionSum
    columnMultiplier columnLoss eta error heta (fun h x j => (hColumnMultiplier h x j).1)
    (fun h x j => (hColumnMultiplier h x j).2) hColumnUnit hColumnPerturb T selectedColumn (fun past => pureComparator_simplex _)
  simp_rw [hRowDirection] at hRow
  simp_rw [hColumnDirection] at hColumn
  have hqSum : ∀ h, ∑ j, q h j = 1 := by
    intro h
    apply SparseMW.normalizedReal_sum hm
    apply SparseMW.rationalHistory_positive
    intro previous x j
    exact (hColumnMultiplier previous x j).1
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
