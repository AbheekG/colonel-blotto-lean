import Blotto.CachedControlWork

/-! A rank-zero state makes no coin request and performs no word work. -/

namespace Blotto.WordStateMachine

theorem cachedControlWork_state_zero_rank {S α : Type*} (m : WordStateMachine S α)
    (tracked : S → Bool) (encodingPrice coinPrice : ℕ → ℕ) (N : ℕ) (bits : Fin N → Bool)
    (state : S) (hRank : m.rank state = 0) (pos : ℕ) (hpos : pos ≤ N) :
    m.cachedControlWork tracked encodingPrice coinPrice N bits (.state state) pos hpos = 0 := by
  conv_lhs => unfold cachedControlWork
  cases hs : m.step state with
  | done value => rfl
  | ask a b hb hab upper lower =>
    have hp := m.progress state
    rw [hs] at hp
    omega

end Blotto.WordStateMachine
