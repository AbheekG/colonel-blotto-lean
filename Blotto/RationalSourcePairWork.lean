import Blotto.RationalResourceMachine
import Blotto.WordMachineIndexedCounts
import Blotto.RealPairProgram

/-! Shared rational pair preparation is charged at most once per source
callback. Coin-bit processing, probability-word extraction, integer arithmetic
and persistent resource-array operations remain separate cost components. -/

namespace Blotto

def rationalSourcePairPreparationWork {n : ℕ} (L r : Fin n → ℚ) (R : ℕ) (bits : Fin R → Bool) : ℕ :=
  RealPairProgram.preparationWork *
    ((rationalResourceMachine L).runCounts R (.ready (RationalActiveResources.initial L r)) bits).callbacks

theorem rationalSourcePairPreparationWork_bound {n : ℕ} (L r : Fin n → ℚ) (R : ℕ) (bits : Fin R → Bool) :
    rationalSourcePairPreparationWork L r R bits ≤ 96 * ((n - 1) + 1) := by
  have hCounts := (rationalResourceMachine L).runCounts_bounds R (n - 1)
    (.ready (RationalActiveResources.initial L r)) (rationalResourceMachine_initial_rank L r) bits
  unfold rationalSourcePairPreparationWork
  rw [RealPairProgram.preparationWork_eq]
  exact Nat.mul_le_mul_left 96 hCounts.1

end Blotto
