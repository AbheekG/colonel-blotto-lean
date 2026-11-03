import Blotto.ProductSecurityConfidence

/-! Two separately trained finite security games have a product history law.
The scheduled sum-gap bad event has probability≤1/8. Continuous reduction,
output empirical error/certification and restart execution remain separate. -/

namespace Blotto
open scoped BigOperators Classical
namespace ProductSecurityTrainer

noncomputable def pairBadGapMean {m n : ℕ} (a : ProductSecurityTrainer m) (b : ProductSecurityTrainer n)
    (TA TB : ℕ) (threshold : ℝ) : ℝ :=
  SparseMW.historyMean a.transition TA (fun ha =>
    SparseMW.historyMean b.transition TB (fun hb => if threshold < a.gap ha + b.gap hb then 1 else 0))

theorem pairBadGapMean_markov {m n : ℕ} (a : ProductSecurityTrainer m) (b : ProductSecurityTrainer n)
    (TA TB : ℕ) (hTA : 0 < TA) (hTB : 0 < TB) (threshold : ℝ) :
    threshold * pairBadGapMean a b TA TB threshold ≤ a.meanGap TA + b.meanGap TB := by
  have hInner : ∀ ha, ha.length = TA →
      threshold * SparseMW.historyMean b.transition TB
        (fun hb => if threshold < a.gap ha + b.gap hb then (1 : ℝ) else 0) ≤ a.gap ha + b.meanGap TB := by
    intro ha hla
    have hpoint : ∀ hb, hb.length = TB →
        threshold * (if threshold < a.gap ha + b.gap hb then (1 : ℝ) else 0) ≤ a.gap ha + b.gap hb := by
      intro hb hlb
      have hA := a.gap_nonnegative ha (by omega)
      have hB := b.gap_nonnegative hb (by omega)
      split_ifs with he
      · simpa only [mul_one] using he.le
      · simpa only [mul_zero] using add_nonneg hA hB
    have he := SparseMW.historyMean_monotone_at_length b.transition b.transition_nonnegative TB _ _ hpoint
    rw [SparseMW.historyMean_mul, SparseMW.historyMean_add,
      SparseMW.historyMean_constant b.transition b.transition_sum] at he
    exact he
  have he := SparseMW.historyMean_monotone_at_length a.transition a.transition_nonnegative TA _ _ hInner
  rw [SparseMW.historyMean_mul, SparseMW.historyMean_add,
    SparseMW.historyMean_constant a.transition a.transition_sum] at he
  exact he

theorem scheduled_pair_bad_gap_bound {m n : ℕ} (a : ProductSecurityTrainer m) (b : ProductSecurityTrainer n)
    (epsilon entropyA entropyB : ℚ) (he : 0 < epsilon ∧ epsilon ≤ 1)
    (hJA : 0 ≤ entropyA) (hJB : 0 ≤ entropyB)
    (hEntropyA : Real.log a.actionsA + Real.log a.actionsB ≤ (entropyA : ℝ))
    (hEntropyB : Real.log b.actionsA + Real.log b.actionsB ≤ (entropyB : ℝ)) :
    pairBadGapMean (a.withAccuracy epsilon he) (b.withAccuracy epsilon he)
      (trainingRounds (epsilon / 2048) epsilon entropyA) (trainingRounds (epsilon / 2048) epsilon entropyB)
      ((epsilon : ℝ) / 8) ≤ 1 / 8 := by
  have hA := a.withAccuracy_expected_gap epsilon entropyA he hJA hEntropyA
  have hB := b.withAccuracy_expected_gap epsilon entropyB he hJB hEntropyB
  have hM := pairBadGapMean_markov (a.withAccuracy epsilon he) (b.withAccuracy epsilon he)
    (trainingRounds (epsilon / 2048) epsilon entropyA) (trainingRounds (epsilon / 2048) epsilon entropyB)
    (trainingRounds_positive _ _ _) (trainingRounds_positive _ _ _) ((epsilon : ℝ) / 8)
  have heR : (0 : ℝ) < (epsilon : ℝ) := by exact_mod_cast he.1
  nlinarith

end ProductSecurityTrainer
end Blotto
