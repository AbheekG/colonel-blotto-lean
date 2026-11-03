import Blotto.WordMachineRefinement

/-! Probability and final-fallback contracts for the state-machine runtime.
The actual runtime law equals the verified tree law while preparation and
sampling execute transitions on states rather than expanding a tree. -/

namespace Blotto.WordStateMachine
open MeasureTheory Set

def output {S α : Type*} (m : WordStateMachine S α) (R : ℕ) (s : S) (fallback : α)
    (bits : Fin R → Bool) : α := (m.run R s bits).1.getD fallback

noncomputable def cappedLaw {S α : Type*} [MeasurableSpace α] (m : WordStateMachine S α)
    (R : ℕ) (s : S) (fallback : α) : ProbabilityMeasure α := (fairBitLaw R).map (m.output R s fallback)

theorem output_refines {S α : Type*} (m : WordStateMachine S α) (R : ℕ) (s : S) (fallback : α)
    (bits : Fin R → Bool) : m.output R s fallback bits = (m.specification s).output R fallback bits := by
  unfold output WordChoiceTree.output
  rw [m.run_refines]

theorem cappedLaw_refines {S α : Type*} [MeasurableSpace α] (m : WordStateMachine S α)
    (R : ℕ) (s : S) (fallback : α) : m.cappedLaw R s fallback = (m.specification s).cappedLaw R fallback := by
  unfold cappedLaw WordChoiceTree.cappedLaw
  congr 1
  exact funext (m.output_refines R s fallback)

theorem failure_probability_precision {S α : Type*} (m : WordStateMachine S α) (C K : ℕ)
    (s : S) (hC : m.rank s ≤ C) :
    (fairBitLaw (3 * (C + K)) : Measure (Fin (3 * (C + K)) → Bool)).real
      {bits | (m.run (3 * (C + K)) s bits).1 = none} ≤ 1 / (2 : ℝ) ^ K := by
  have he : {bits : Fin (3 * (C + K)) → Bool | (m.run (3 * (C + K)) s bits).1 = none} =
      {bits | ((m.specification s).sample (3 * (C + K)) bits).1 = none} := by
    ext bits
    simp only [mem_ofPred_eq, m.run_refines]
  rw [he]
  exact (m.specification s).failure_probability_precision C K ((m.specification_height s).trans hC)

theorem cappedLaw_event_error_precision {S α : Type*} [MeasurableSpace α] (m : WordStateMachine S α)
    (C K : ℕ) (s : S) (hC : m.rank s ≤ C) (fallback : α) (A : Set α) (hA : MeasurableSet A) :
    |(m.cappedLaw (3 * (C + K)) s fallback : Measure α).real A -
      ((m.specification s).decode.idealLaw : Measure α).real A| ≤ 1 / (2 : ℝ) ^ K := by
  rw [m.cappedLaw_refines]
  exact (m.specification s).cappedLaw_event_error_precision C K ((m.specification_height s).trans hC) fallback A hA

theorem specification_forLeaves {S α : Type*} (m : WordStateMachine S α) (I : S → Prop) (P : α → Prop)
    (hI : ∀ s, I s → match m.step s with
      | .done value => P value
      | .ask _ _ _ _ upper lower => I upper ∧ I lower) (s : S) (hs : I s) :
    (m.specification s).decode.ForLeaves P := by
  have hAll : ∀ n, ∀ s : S, m.rank s = n → I s → (m.specification s).decode.ForLeaves P := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro s he hs
      unfold specification
      split
      · rename_i value hstep
        have hp := hI s hs
        rw [hstep] at hp
        exact hp
      · rename_i a b hb hab upper lower hstep
        have hprogress := m.progress s
        have hnext := hI s hs
        rw [hstep] at hprogress hnext
        exact ⟨ih (m.rank upper) (by omega) upper rfl hnext.1,
          ih (m.rank lower) (by omega) lower rfl hnext.2⟩
  exact hAll (m.rank s) s rfl hs

theorem output_invariant {S α : Type*} (m : WordStateMachine S α) (R : ℕ) (s : S) (fallback : α)
    (bits : Fin R → Bool) (I : S → Prop) (P : α → Prop)
    (hI : ∀ s, I s → match m.step s with
      | .done value => P value
      | .ask _ _ _ _ upper lower => I upper ∧ I lower) (hs : I s) (hd : P fallback) :
    P (m.output R s fallback bits) := by
  rw [m.output_refines]
  exact (m.specification s).output_forLeaves R fallback bits P (m.specification_forLeaves I P hI s hs) hd

theorem accepted_invariant {S α : Type*} (m : WordStateMachine S α) (R : ℕ) (s : S)
    (bits : Fin R → Bool) (I : S → Prop) (P : α → Prop)
    (hI : ∀ s, I s → match m.step s with
      | .done value => P value
      | .ask _ _ _ _ upper lower => I upper ∧ I lower) (hs : I s) {value : α}
    (hv : (m.run R s bits).1 = some value) : P value := by
  rw [m.run_refines, (m.specification s).sample_refines] at hv
  exact (m.specification s).decode.sample_forLeaves R bits P (m.specification_forLeaves I P hI s hs) hv

theorem specification_mean {S α : Type*} (m : WordStateMachine S α) (value : S → ℝ) (f : α → ℝ)
    (hvalue : ∀ s, match m.step s with
      | .done x => f x = value s
      | .ask a b _ _ upper lower => value s = ((a : ℚ) / b : ℝ) * value upper +
          (1 - ((a : ℚ) / b : ℝ)) * value lower) (s : S) :
    (m.specification s).decode.mean f = value s := by
  have hAll : ∀ n, ∀ s : S, m.rank s = n → (m.specification s).decode.mean f = value s := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro s he
      unfold specification
      split
      · rename_i x hstep
        have hv := hvalue s
        rw [hstep] at hv
        exact hv
      · rename_i a b hb hab upper lower hstep
        have hp := m.progress s
        have hv := hvalue s
        rw [hstep] at hp hv
        have hu := ih (m.rank upper) (by omega) upper rfl
        have hl := ih (m.rank lower) (by omega) lower rfl
        simp only [WordChoiceTree.decode, AdaptiveChoiceTree.mean]
        rw [hu, hl]
        simpa only [Rat.cast_div, Rat.cast_natCast] using hv.symm
  exact hAll (m.rank s) s rfl

end Blotto.WordStateMachine
