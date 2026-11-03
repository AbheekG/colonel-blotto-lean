import Blotto.ProductSecuritySchedule

/-! The exact finite trainer's scheduled expected-gap bound yields a finite
bad-event probability. This is a training guarantee, not continuous output
certification or an independent-restart runtime theorem. -/

namespace Blotto
open scoped BigOperators Classical
namespace ProductSecurityTrainer

noncomputable def gap {m : ℕ} (c : ProductSecurityTrainer m) (past : List (Fin c.observations)) : ℝ :=
  FiniteSaddle.GapAt c.matrix (FiniteSaddle.historyAverage (fun h => (c.lawA h).realWeight) past)
    (FiniteSaddle.historyAverage (fun h => (c.lawB h).realWeight) past)
    (FiniteSaddle.minimizingRow c.actionsA_positive c.matrix
      (FiniteSaddle.historyAverage (fun h => (c.lawB h).realWeight) past))
    (FiniteSaddle.maximizingColumn c.actionsB_positive c.matrix
      (FiniteSaddle.historyAverage (fun h => (c.lawA h).realWeight) past))

theorem gap_nonnegative {m : ℕ} (c : ProductSecurityTrainer m) (past : List (Fin c.observations))
    (hPast : 0 < past.length) : 0 ≤ c.gap past := by
  have he := FiniteSaddle.both_regrets_le_gap c.actionsA_positive c.actionsB_positive c.matrix
    (FiniteSaddle.historyAverage (fun h => (c.lawA h).realWeight) past)
    (FiniteSaddle.historyAverage (fun h => (c.lawB h).realWeight) past)
    (FiniteSaddle.historyAverage_nonnegative _ (fun h i => (c.lawA h).realWeight_nonnegative i) past)
    (FiniteSaddle.historyAverage_total _ (fun h => (c.lawA h).realWeight_sum) past hPast)
    (FiniteSaddle.historyAverage_nonnegative _ (fun h j => (c.lawB h).realWeight_nonnegative j) past)
    (FiniteSaddle.historyAverage_total _ (fun h => (c.lawB h).realWeight_sum) past hPast)
  exact he.1

noncomputable def badGapMean {m : ℕ} (c : ProductSecurityTrainer m) (T : ℕ) (threshold : ℝ) : ℝ :=
  SparseMW.historyMean c.transition T (fun past => if threshold < c.gap past then 1 else 0)

theorem badGapMean_markov {m : ℕ} (c : ProductSecurityTrainer m) (T : ℕ) (hT : 0 < T)
    (threshold : ℝ) (_hthreshold : 0 < threshold) : threshold * c.badGapMean T threshold ≤ c.meanGap T := by
  have hpath : ∀ past, past.length = T →
      threshold * (if threshold < c.gap past then (1 : ℝ) else 0) ≤ c.gap past := by
    intro past hlength
    have hg := c.gap_nonnegative past (by omega)
    split_ifs with h
    · simpa only [mul_one] using h.le
    · simpa only [mul_zero] using hg
  have he := SparseMW.historyMean_monotone_at_length c.transition c.transition_nonnegative T _ _ hpath
  rw [SparseMW.historyMean_mul] at he
  exact he

theorem withAccuracy_bad_gap_bound {m : ℕ} (c : ProductSecurityTrainer m) (epsilon entropy : ℚ)
    (he : 0 < epsilon ∧ epsilon ≤ 1) (hJ : 0 ≤ entropy)
    (hEntropy : Real.log c.actionsA + Real.log c.actionsB ≤ (entropy : ℝ)) :
    (c.withAccuracy epsilon he).badGapMean (trainingRounds (epsilon / 2048) epsilon entropy) ((epsilon : ℝ) / 8) ≤ 1 / 16 := by
  have hs := c.withAccuracy_expected_gap epsilon entropy he hJ hEntropy
  have hm := (c.withAccuracy epsilon he).badGapMean_markov (trainingRounds (epsilon / 2048) epsilon entropy)
    (trainingRounds_positive _ _ _) ((epsilon : ℝ) / 8) (by exact_mod_cast div_pos he.1 (by norm_num : (0 : ℚ) < 8))
  have heR : (0 : ℝ) < (epsilon : ℝ) := by exact_mod_cast he.1
  nlinarith

end ProductSecurityTrainer
end Blotto
