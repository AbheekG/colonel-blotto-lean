import Blotto.SharedResourceRefinement
import Blotto.RationalResourceContracts
import Blotto.RationalResourceLatticeMachine

/-! Existing all-path resource contracts and cap-failure bounds transfer to
the one-state interpreter through exact value/position refinement. -/

namespace Blotto.SharedResourceCursor
open MeasureTheory

theorem accepted_terminal_contract {n : ℕ} (L : Fin n → ℚ) (total : ℝ) (state : RationalActiveResources L)
    (hState : RationalResourceInvariant L total state) (R : ℕ) (bits : Fin R → Bool)
    {result : RationalActiveResources L} (hResult : (run R state bits).1 = some result) :
    InBox (fun j => (L j : ℝ)) result.resource.realAllocation ∧
      (∑ j, result.resource.realAllocation j) = total ∧
      (fractionalSet (fun j => (L j : ℝ)) result.resource.realAllocation).card ≤ 1 := by
  rw [run_refines] at hResult
  exact rationalResourceMachine_terminal_contract L total (.ready state) R bits hState hResult

theorem accepted_lattice {n : ℕ} (L : Fin n → ℚ) (D : ℕ) (hL : ∀ j, OnRationalLattice D (L j))
    (state : RationalActiveResources L) (hState : state.resource.OnLattice D) (R : ℕ) (bits : Fin R → Bool)
    {result : RationalActiveResources L} (hResult : (run R state bits).1 = some result) :
    result.resource.OnLattice D := by
  rw [run_refines] at hResult
  exact rationalResourceMachine_lattice_completed L D hL (.ready state) R bits hState hResult

theorem failure_probability_precision {n : ℕ} (L r : Fin n → ℚ) (K : ℕ) :
    (fairBitLaw (3 * (n - 1 + K)) : Measure (Fin (3 * (n - 1 + K)) → Bool)).real
      {bits | (run (3 * (n - 1 + K)) (RationalActiveResources.initial L r) bits).1 = none} ≤ 1 / (2 : ℝ) ^ K := by
  simpa only [run_refines] using rationalResourceMachine_failure_probability L r K

end Blotto.SharedResourceCursor
