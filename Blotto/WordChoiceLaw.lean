import Blotto.WordChoiceTree
import Blotto.AdaptiveChoiceFallback

/-! Actual output law and statistical contracts of the integer shared-cap
interpreter. The refined rational tree is the ideal semantics, not an
assumption that the PRG program has already been compiled into this form. -/

namespace Blotto.WordChoiceTree
open MeasureTheory Set

def output {α : Type*} (R : ℕ) (T : WordChoiceTree α) (fallback : α) (bits : Fin R → Bool) : α :=
  (T.sample R bits).1.getD fallback

noncomputable def cappedLaw {α : Type*} [MeasurableSpace α] (R : ℕ) (T : WordChoiceTree α) (fallback : α) :
    ProbabilityMeasure α := (fairBitLaw R).map (T.output R fallback)

theorem output_refines {α : Type*} (R : ℕ) (T : WordChoiceTree α) (fallback : α) (bits : Fin R → Bool) :
    T.output R fallback bits = T.decode.output R fallback bits := by
  unfold output AdaptiveChoiceTree.output
  rw [T.sample_refines]

theorem cappedLaw_refines {α : Type*} [MeasurableSpace α] (R : ℕ) (T : WordChoiceTree α) (fallback : α) :
    T.cappedLaw R fallback = T.decode.cappedLaw R fallback := by
  unfold cappedLaw AdaptiveChoiceTree.cappedLaw
  congr 1
  exact funext (T.output_refines R fallback)

theorem failure_probability_precision {α : Type*} (C K : ℕ) (T : WordChoiceTree α) (hC : T.height ≤ C) :
    (fairBitLaw (3 * (C + K)) : Measure (Fin (3 * (C + K)) → Bool)).real
      {bits | (T.sample (3 * (C + K)) bits).1 = none} ≤ 1 / (2 : ℝ) ^ K := by
  have he : {bits : Fin (3 * (C + K)) → Bool | (T.sample (3 * (C + K)) bits).1 = none} =
      {bits | (T.decode.sample (3 * (C + K)) bits).1 = none} := by
    ext bits
    simp only [mem_ofPred_eq, T.sample_refines]
  rw [he]
  exact T.decode.sample_precision_cap C K (by simpa only [T.decode_height] using hC)

theorem cappedLaw_event_error_precision {α : Type*} [MeasurableSpace α] (C K : ℕ)
    (T : WordChoiceTree α) (hC : T.height ≤ C) (fallback : α) (A : Set α) (hA : MeasurableSet A) :
    |(T.cappedLaw (3 * (C + K)) fallback : Measure α).real A - (T.decode.idealLaw : Measure α).real A| ≤ 1 / (2 : ℝ) ^ K := by
  rw [T.cappedLaw_refines]
  exact T.decode.cappedLaw_event_error_precision C K (by simpa only [T.decode_height] using hC) fallback A hA

theorem output_forLeaves {α : Type*} (R : ℕ) (T : WordChoiceTree α) (fallback : α) (bits : Fin R → Bool)
    (P : α → Prop) (hT : T.decode.ForLeaves P) (hd : P fallback) : P (T.output R fallback bits) := by
  rw [T.output_refines]
  exact T.decode.output_forLeaves R fallback bits P hT hd

end Blotto.WordChoiceTree
