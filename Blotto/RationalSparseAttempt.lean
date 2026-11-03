import Blotto.RationalImportanceAttempt

/-! Finite-bit attempts reject zero-probability record labels explicitly.
This makes every accepted bit path inherit positive-record feasibility. The
ideal law is unchanged because discarded labels carry zero rational weight. -/

namespace Blotto
open scoped BigOperators Classical
namespace RationalImportanceData

def safeAttempt {r n : ℕ} (q : RationalImportanceData r n) (bound : ℚ)
    (hb : 0 < bound) (h : ∀ p, q.importance p ≤ bound) (fallback : Fin r) : RationalFiniteAttempt (r * 2) n :=
  let a := q.attempt bound hb h fallback
  { a with decode := fun i => if 0 < q.probability (finProdFinEquiv.symm i).1 then a.decode i else none }

theorem safeAttempt_accepted_positive {r n : ℕ} (q : RationalImportanceData r n) (bound : ℚ)
    (hb : 0 < bound) (h : ∀ p, q.importance p ≤ bound) (fallback : Fin r)
    (i : Fin (r * 2)) (x : Fin n) (hx : (q.safeAttempt bound hb h fallback).decode i = some x) :
    ∃ p, 0 < q.probability p ∧ q.output p = x := by
  unfold safeAttempt at hx
  dsimp only at hx
  split at hx
  · rename_i hp
    unfold attempt at hx
    dsimp only at hx
    split at hx
    · exact ⟨_, hp, Option.some.inj hx⟩
    · cases hx
  · cases hx

theorem safeAttempt_bitpath_feasible {r n : ℕ} (q : RationalImportanceData r n) (predicate : Fin n → Prop)
    (hFeasible : ∀ p, 0 < q.probability p → predicate (q.output p)) (bound : ℚ) (hb : 0 < bound)
    (h : ∀ p, q.importance p ≤ bound) (fallbackRecord : Fin r) (fallbackOutput : Fin n)
    (hf : predicate fallbackOutput) (K : ℕ)
    (bits : Fin ((q.safeAttempt bound hb h fallbackRecord).bitBudget K) → Bool) :
    predicate (((q.safeAttempt bound hb h fallbackRecord).sample K bits).getD fallbackOutput) := by
  cases he : (q.safeAttempt bound hb h fallbackRecord).sample K bits with
  | none => exact hf
  | some x =>
    rcases q.safeAttempt_accepted_positive bound hb h fallbackRecord _ x he with ⟨p, hp, hx⟩
    exact hx ▸ hFeasible p hp

theorem safeAttempt_idealEvent_eq {r n : ℕ} (q : RationalImportanceData r n) (bound : ℚ)
    (hb : 0 < bound) (h : ∀ p, q.importance p ≤ bound) (fallback : Fin r)
    (event : Set (Option (Fin n))) :
    (q.safeAttempt bound hb h fallback).idealEventProbability event =
      (q.attempt bound hb h fallback).idealEventProbability event := by
  unfold RationalFiniteAttempt.idealEventProbability safeAttempt
  dsimp only
  apply Finset.sum_congr rfl
  intro i _
  by_cases hp : 0 < q.probability (finProdFinEquiv.symm i).1
  · simp only [hp, ite_true]
  · have hz : q.probability (finProdFinEquiv.symm i).1 = 0 :=
      le_antisymm (le_of_not_gt hp) (q.probability_nonnegative _)
    simp only [attempt, hz, zero_mul, Rat.cast_zero]

theorem safeAttempt_event_error {r n : ℕ} (q : RationalImportanceData r n) (bound : ℚ)
    (hb : 0 < bound) (h : ∀ p, q.importance p ≤ bound) (fallback : Fin r) (K : ℕ)
    (event : Set (Option (Fin n))) :
    |(q.safeAttempt bound hb h fallback).eventProbability K event -
      (q.attempt bound hb h fallback).idealEventProbability event| ≤ 1 / (2 : ℝ) ^ K := by
  rw [← q.safeAttempt_idealEvent_eq bound hb h fallback event]
  exact (q.safeAttempt bound hb h fallback).eventProbability_error K event

end RationalImportanceData
end Blotto
