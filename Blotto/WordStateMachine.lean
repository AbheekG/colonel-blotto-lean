import Blotto.WordStateMachineCore
import Blotto.CachedWordControllerRefinement

/-! Public controller entry: each new coin encodes its words once; pending
iterations retain the denominator and use Boolean arithmetic. The numeric
indexed loop remains the exact proof/refinement reference. -/

namespace Blotto.WordStateMachine

def run {S α : Type*} (m : WordStateMachine S α) (R : ℕ) (s : S) (bits : Fin R → Bool) : Option α × ℕ :=
  m.runCachedIndexed R bits (.state s) 0 (Nat.zero_le R)

theorem run_eq_numeric {S α : Type*} (m : WordStateMachine S α) (R : ℕ) (s : S) (bits : Fin R → Bool) :
    m.run R s bits = m.runNumeric R s bits :=
  m.runCachedIndexed_refines R bits (.state s) 0 (Nat.zero_le R)

end Blotto.WordStateMachine
