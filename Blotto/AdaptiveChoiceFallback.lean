import Blotto.AdaptiveChoiceDomination
import Blotto.AdaptiveChoiceFailure

/-! An actual bounded fair-bit output law with an arbitrary final fallback.
Every event probability differs from the ideal adaptive law by at most the
shared-cap exhaustion probability; the proof uses accepted-law domination. -/

namespace Blotto.AdaptiveChoiceTree
open MeasureTheory Set
open scoped Classical

noncomputable def eventValue {α : Type*} (A : Set α) (x : α) : ℝ := if x ∈ A then 1 else 0

noncomputable def acceptedProbability {α : Type*} (R : ℕ) (T : AdaptiveChoiceTree α) (A : Set α) : ℝ :=
  ∫ bits, acceptedValue (eventValue A) (T.sample R bits).1 ∂(fairBitLaw R : Measure (Fin R → Bool))

noncomputable def failureProbability {α : Type*} (R : ℕ) (T : AdaptiveChoiceTree α) : ℝ :=
  (fairBitLaw R : Measure (Fin R → Bool)).real {bits | (T.sample R bits).1 = none}

theorem failureProbability_integral {α : Type*} (R : ℕ) (T : AdaptiveChoiceTree α) :
    T.failureProbability R = ∫ bits, (if (T.sample R bits).1 = none then (1 : ℝ) else 0)
      ∂(fairBitLaw R : Measure (Fin R → Bool)) := by
  let A : Set (Fin R → Bool) := {bits | (T.sample R bits).1 = none}
  have hA : MeasurableSet A := A.to_countable.measurableSet
  have he : (fun bits : Fin R → Bool => if (T.sample R bits).1 = none then (1 : ℝ) else 0) =
      A.indicator (fun _ => (1 : ℝ)) := by funext bits; simp [A, Set.indicator_apply]
  rw [he, integral_indicator_const _ hA, smul_eq_mul, mul_one]
  rfl

theorem acceptedProbability_partition {α : Type*} (R : ℕ) (T : AdaptiveChoiceTree α) (A : Set α) :
    T.acceptedProbability R A + T.acceptedProbability R Aᶜ + T.failureProbability R = 1 := by
  have he : (fun bits : Fin R → Bool => acceptedValue (eventValue A) (T.sample R bits).1 +
      acceptedValue (eventValue Aᶜ) (T.sample R bits).1 + if (T.sample R bits).1 = none then 1 else 0) =
      fun _ => (1 : ℝ) := by
    funext bits
    cases hs : (T.sample R bits).1 with
    | none => simp [acceptedValue]
    | some x => by_cases hx : x ∈ A <;> simp [acceptedValue, eventValue, hx]
  rw [acceptedProbability, acceptedProbability, failureProbability_integral,
    ← integral_add Integrable.of_finite Integrable.of_finite, ← integral_add Integrable.of_finite Integrable.of_finite,
    he, integral_const, probReal_univ, one_smul]

theorem acceptedProbability_le_ideal {α : Type*} [MeasurableSpace α] (R : ℕ) (T : AdaptiveChoiceTree α)
    (A : Set α) (hA : MeasurableSet A) : T.acceptedProbability R A ≤ (T.idealLaw : Measure α).real A := by
  rw [idealLaw_real_event _ _ hA]
  exact T.sample_accepted_le_mean R (eventValue A) (fun x => by unfold eventValue; split_ifs <;> norm_num)

def output {α : Type*} (R : ℕ) (T : AdaptiveChoiceTree α) (fallback : α) (bits : Fin R → Bool) : α :=
  (T.sample R bits).1.getD fallback

noncomputable def cappedLaw {α : Type*} [MeasurableSpace α] (R : ℕ) (T : AdaptiveChoiceTree α)
    (fallback : α) : ProbabilityMeasure α := (fairBitLaw R).map (T.output R fallback)

theorem cappedLaw_event {α : Type*} [MeasurableSpace α] (R : ℕ) (T : AdaptiveChoiceTree α) (fallback : α)
    (A : Set α) (hA : MeasurableSet A) :
    (T.cappedLaw R fallback : Measure α).real A = T.acceptedProbability R A + eventValue A fallback * T.failureProbability R := by
  have hf : Measurable (T.output R fallback) := measurable_of_countable _
  have hi : (∫ bits, eventValue A (T.output R fallback bits) ∂(fairBitLaw R : Measure (Fin R → Bool))) =
      (fairBitLaw R : Measure (Fin R → Bool)).real ((T.output R fallback) ⁻¹' A) := by
    have he : (fun bits : Fin R → Bool => eventValue A (T.output R fallback bits)) =
        ((T.output R fallback) ⁻¹' A).indicator (fun _ => (1 : ℝ)) := by
      funext bits
      simp [eventValue, Set.indicator_apply]
    rw [he, integral_indicator_const _ (hA.preimage hf), smul_eq_mul, mul_one]
  have he : (fun bits : Fin R → Bool => eventValue A (T.output R fallback bits)) =
      fun bits => acceptedValue (eventValue A) (T.sample R bits).1 +
        eventValue A fallback * (if (T.sample R bits).1 = none then 1 else 0) := by
    funext bits
    cases hs : (T.sample R bits).1 <;> simp [output, hs, acceptedValue]
  change (Measure.map (T.output R fallback) (fairBitLaw R : Measure (Fin R → Bool))).real A = _
  rw [map_measureReal_apply hf hA, ← hi, he, integral_add Integrable.of_finite Integrable.of_finite,
    integral_const_mul, ← failureProbability_integral]
  rfl

theorem cappedLaw_event_error {α : Type*} [MeasurableSpace α] (R : ℕ) (T : AdaptiveChoiceTree α) (fallback : α)
    (A : Set α) (hA : MeasurableSet A) :
    |(T.cappedLaw R fallback : Measure α).real A - (T.idealLaw : Measure α).real A| ≤ T.failureProbability R := by
  have ha := T.acceptedProbability_le_ideal R A hA
  have hac := T.acceptedProbability_le_ideal R Aᶜ hA.compl
  have hs := T.acceptedProbability_partition R A
  rw [measureReal_compl hA, probReal_univ] at hac
  rw [T.cappedLaw_event R fallback A hA]
  have hn : 0 ≤ T.failureProbability R := measureReal_nonneg
  by_cases hd : fallback ∈ A
  · simp only [eventValue, hd, ite_true, one_mul]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  · simp only [eventValue, hd, ite_false, zero_mul, add_zero]
    exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem cappedLaw_event_error_precision {α : Type*} [MeasurableSpace α] (C K : ℕ) (T : AdaptiveChoiceTree α)
    (hC : T.height ≤ C) (fallback : α) (A : Set α) (hA : MeasurableSet A) :
    |(T.cappedLaw (3 * (C + K)) fallback : Measure α).real A - (T.idealLaw : Measure α).real A| ≤ 1 / (2 : ℝ) ^ K :=
  (T.cappedLaw_event_error _ fallback A hA).trans (T.sample_precision_cap C K hC)

theorem output_forLeaves {α : Type*} (R : ℕ) (T : AdaptiveChoiceTree α) (fallback : α) (bits : Fin R → Bool)
    (P : α → Prop) (hT : T.ForLeaves P) (hd : P fallback) : P (T.output R fallback bits) := by
  cases hs : (T.sample R bits).1 with
  | none => simpa only [output, hs, Option.getD_none] using hd
  | some x =>
    have hx := T.sample_forLeaves R bits P hT hs
    simpa only [output, hs, Option.getD_some] using hx

end Blotto.AdaptiveChoiceTree
