import Blotto.AdaptiveChoiceMoment
import Blotto.PRGApproximation

/-! Actual shared-cap failure probabilities. Exhaustion consumes exactly R
bits, so the exponential moment gives 2^C*(3/4)^R for a height-C adaptive
program. The prescribed cap 3(C+K) has failure probability at most 2^-K. -/

namespace Blotto.AdaptiveChoiceTree
open MeasureTheory Set
open scoped Classical

theorem sample_failure_probability {α : Type*} (R : ℕ) (T : AdaptiveChoiceTree α) :
    (fairBitLaw R : Measure (Fin R → Bool)).real {bits | (T.sample R bits).1 = none} ≤
      (2 : ℝ) ^ T.height * (3 / 4 : ℝ) ^ R := by
  let A : Set (Fin R → Bool) := {bits | (T.sample R bits).1 = none}
  have hA : MeasurableSet A := A.to_countable.measurableSet
  have hpt : (fun bits : Fin R → Bool => A.indicator (fun _ => (4 / 3 : ℝ) ^ R) bits) ≤
      (fun bits => (4 / 3 : ℝ) ^ (T.sample R bits).2) := by
    intro bits
    by_cases hn : (T.sample R bits).1 = none
    · have hs := T.sample_none_bits R bits hn
      simp [A, hn, hs]
    · simp [A, hn, pow_nonneg (by norm_num : (0 : ℝ) ≤ 4 / 3)]
  have hi := integral_mono (μ := (fairBitLaw R : Measure (Fin R → Bool)))
    Integrable.of_finite Integrable.of_finite hpt
  rw [integral_indicator_const _ hA, smul_eq_mul] at hi
  have hm := T.sample_moment R
  have hp : (0 : ℝ) < (4 / 3) ^ R := pow_pos (by norm_num) _
  have hbound : (fairBitLaw R : Measure (Fin R → Bool)).real A ≤ (2 : ℝ) ^ T.height / (4 / 3 : ℝ) ^ R :=
    (le_div_iff₀ hp).mpr (hi.trans hm)
  have he : (2 : ℝ) ^ T.height / (4 / 3 : ℝ) ^ R = (2 : ℝ) ^ T.height * (3 / 4 : ℝ) ^ R := by
    rw [div_eq_mul_inv, ← inv_pow]
    congr 1
    norm_num
  rw [he] at hbound
  exact hbound

theorem sample_failure_probability_of_height {α : Type*} (R C : ℕ) (T : AdaptiveChoiceTree α)
    (hC : T.height ≤ C) :
    (fairBitLaw R : Measure (Fin R → Bool)).real {bits | (T.sample R bits).1 = none} ≤
      (2 : ℝ) ^ C * (3 / 4 : ℝ) ^ R :=
  (T.sample_failure_probability R).trans
    (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hC) (pow_nonneg (by norm_num) _))

theorem sample_precision_cap {α : Type*} (C K : ℕ) (T : AdaptiveChoiceTree α) (hC : T.height ≤ C) :
    (fairBitLaw (3 * (C + K)) : Measure (Fin (3 * (C + K)) → Bool)).real
      {bits | (T.sample (3 * (C + K)) bits).1 = none} ≤ 1 / (2 : ℝ) ^ K := by
  have he := (T.sample_failure_probability_of_height (3 * (C + K)) C hC).trans (prg_branch_cap_algebra C K)
  simpa only [one_div_pow] using he

end Blotto.AdaptiveChoiceTree
