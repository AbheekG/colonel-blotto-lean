import Blotto.AdaptiveChoiceFallback

/-! Shared-cap exhaustion controls the expectation of every [0,1]-valued
test, not only indicator events. This permits adaptive kernel composition
without multiplying errors by the number of output labels. -/

namespace Blotto.AdaptiveChoiceTree
open MeasureTheory

theorem mean_complement {α : Type*} (T : AdaptiveChoiceTree α) (f : α → ℝ) :
    T.mean (fun x => 1 - f x) = 1 - T.mean f := by
  induction T with
  | leaf x => rfl
  | fork p hp upper lower ihU ihL =>
    simp only [mean, ihU, ihL]
    ring

theorem capped_mean_error {α : Type*} (R : ℕ) (T : AdaptiveChoiceTree α)
    (fallback : α) (f : α → ℝ) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) :
    |(∫ bits, f (T.output R fallback bits) ∂(fairBitLaw R : Measure (Fin R → Bool))) - T.mean f| ≤
      T.failureProbability R := by
  have hLow := T.sample_accepted_le_mean R f (fun x => (hf x).1)
  have hHigh := T.sample_accepted_le_mean R (fun x => 1 - f x) (fun x => by linarith [(hf x).2])
  rw [T.mean_complement] at hHigh
  have hpart : (∫ bits, acceptedValue f (T.sample R bits).1 ∂(fairBitLaw R : Measure (Fin R → Bool))) +
      (∫ bits, acceptedValue (fun x => 1 - f x) (T.sample R bits).1 ∂(fairBitLaw R : Measure (Fin R → Bool))) +
        T.failureProbability R = 1 := by
    rw [T.failureProbability_integral, ← integral_add Integrable.of_finite Integrable.of_finite,
      ← integral_add Integrable.of_finite Integrable.of_finite]
    have he : (fun bits : Fin R → Bool => acceptedValue f (T.sample R bits).1 +
        acceptedValue (fun x => 1 - f x) (T.sample R bits).1 +
          if (T.sample R bits).1 = none then 1 else 0) = fun _ => (1 : ℝ) := by
      funext bits
      cases h : (T.sample R bits).1 <;> simp [acceptedValue]
    rw [he, integral_const, probReal_univ, one_smul]
  have hOut : (∫ bits, f (T.output R fallback bits) ∂(fairBitLaw R : Measure (Fin R → Bool))) =
      (∫ bits, acceptedValue f (T.sample R bits).1 ∂(fairBitLaw R : Measure (Fin R → Bool))) +
        f fallback * T.failureProbability R := by
    have he : (fun bits : Fin R → Bool => f (T.output R fallback bits)) =
        fun bits => acceptedValue f (T.sample R bits).1 +
          f fallback * (if (T.sample R bits).1 = none then 1 else 0) := by
      funext bits
      cases h : (T.sample R bits).1 <;> simp [output, h, acceptedValue]
    rw [he, integral_add Integrable.of_finite Integrable.of_finite, integral_const_mul,
      ← T.failureProbability_integral]
  have hn : 0 ≤ T.failureProbability R := measureReal_nonneg
  rw [hOut, abs_le]
  constructor <;> nlinarith [(hf fallback).1, (hf fallback).2]

theorem capped_mean_error_precision {α : Type*} (C K : ℕ) (T : AdaptiveChoiceTree α)
    (hC : T.height ≤ C) (fallback : α) (f : α → ℝ) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) :
    |(∫ bits, f (T.output (3 * (C + K)) fallback bits)
        ∂(fairBitLaw (3 * (C + K)) : Measure (Fin (3 * (C + K)) → Bool))) - T.mean f| ≤ 1 / (2 : ℝ) ^ K :=
  (T.capped_mean_error _ fallback f hf).trans (T.sample_precision_cap C K hC)

end Blotto.AdaptiveChoiceTree
