import Blotto.WordMachineMap

/-! Equal transition and rank fields determine a word controller; its
progress certificates are proofs. Closure preparation may change while
preserving every indexed path and its existing mathematical contracts. -/

namespace Blotto.WordStateMachine

theorem eq_of_runtime_fields {S α : Type*} (m n : WordStateMachine S α)
    (hStep : m.step = n.step) (hRank : m.rank = n.rank) : m = n := by
  cases m
  cases n
  cases hStep
  cases hRank
  rfl

end Blotto.WordStateMachine
