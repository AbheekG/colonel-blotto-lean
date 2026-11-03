import Blotto.CachedTrackedEncodingWork
import Blotto.CachedWordReindex

/-! A single controller-work observer prices each new tracked word encoding
and each tracked Boolean coin body on the indexed production path. The two
prices are arbitrary; no state callback, address or backend price is included. -/

namespace Blotto.WordStateMachine

def cachedControlWork {S α : Type*} (m : WordStateMachine S α) (tracked : S → Bool) (encodingPrice coinPrice : ℕ → ℕ) (N : ℕ) (bits : Fin N → Bool)
    (cursor : CachedWordCursor S) (pos : ℕ) (hpos : pos ≤ N) : ℕ :=
  match cursor with
  | .state s =>
    match _hs : m.step s with
    | .done _ => 0
    | .ask a b hb hab upper lower =>
      (if trackedCoin tracked upper lower then encodingPrice (binaryWordWidth b) else 0) + m.cachedControlWork tracked encodingPrice coinPrice N bits (.ofWords a b hb hab upper lower) pos hpos
  | @CachedWordCursor.coin _ w a b hb hab upper lower =>
    (if trackedCoin tracked upper lower then coinPrice w else 0) +
      if hz : a.isZero = true then m.cachedControlWork tracked encodingPrice coinPrice N bits (.state lower) pos hpos else
      if he : a.same b = true then m.cachedControlWork tracked encodingPrice coinPrice N bits (.state upper) pos hpos else
        if hRead : pos < N then
          let next := a.coinStep b
          have hlt : a.value < b.value := lt_of_le_of_ne hab (fun h => he ((a.same_value b).mpr h))
          if bits ⟨pos, hRead⟩ = next.1 then
            m.cachedControlWork tracked encodingPrice coinPrice N bits (.coin next.2 b hb (a.coinStep_normalized b hlt).le upper lower)
              (pos + 1) (by omega)
          else m.cachedControlWork tracked encodingPrice coinPrice N bits (.state (if bits ⟨pos, hRead⟩ then lower else upper))
            (pos + 1) (by omega)
        else 0
termination_by (N - pos, m.cachedCursorRank cursor)
decreasing_by
  all_goals simp only [cachedCursorRank]
  · have hp := m.progress s
    rw [_hs] at hp
    simp only [CachedWordCursor.ofWords]
    omega
  all_goals omega


end Blotto.WordStateMachine
