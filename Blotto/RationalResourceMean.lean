import Blotto.RationalResourceContracts

/-! Exact coefficient preservation of the concrete resource state machine.
Its ideal semantics averages every terminal resource coordinate to the
initial one, using the verified decoded pair lottery at each transition. -/

namespace Blotto

theorem rationalResourceStep_expectation {n : ℕ} {L : Fin n → ℚ} (s : RationalActiveResources L) (j : Fin n) :
    match rationalResourceStep s with
    | .done value => value.resource.realAllocation j = s.resource.realAllocation j
    | .ask a b _ _ upper lower => s.resource.realAllocation j =
        ((a : ℚ) / b : ℝ) * upper.materialize.resource.realAllocation j +
          (1 - ((a : ℚ) / b : ℝ)) * lower.materialize.resource.realAllocation j := by
  rw [rationalResourceStep_refines]
  cases s with
  | mk resource active hn hm =>
    cases active with
    | nil => rfl
    | cons a rest =>
      cases rest with
      | nil => rfl
      | cons b tail =>
        let s : RationalActiveResources L := ⟨resource, a :: b :: tail, hn, hm⟩
        dsimp only [rationalResourceStepReference, RationalResourceCursor.materialize]
        simpa only [ProbabilityWords.rational, Rat.cast_div, Rat.cast_natCast, s] using
          (s.update_expectation a b tail rfl j).symm

theorem rationalResourceMachine_mean {n : ℕ} (L : Fin n → ℚ) (cursor : RationalResourceCursor L) (j : Fin n) :
    ((rationalResourceMachine L).specification cursor).decode.mean (fun s => s.resource.realAllocation j) =
      cursor.materialize.resource.realAllocation j := by
  apply (rationalResourceMachine L).specification_mean (fun c => c.materialize.resource.realAllocation j)
    (fun s => s.resource.realAllocation j)
  intro c
  have hp := rationalResourceStep_expectation c.materialize j
  unfold rationalResourceMachine rationalResourceTransition
  dsimp only
  cases hs : rationalResourceStep c.materialize with
  | done value => rw [hs] at hp; exact hp
  | ask a b hb hab upper lower => rw [hs] at hp; exact hp

end Blotto
