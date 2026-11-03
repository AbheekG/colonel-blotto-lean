import Blotto.CachedWordCursor
import Blotto.WordMachineSerial

/-! Renaming controller states preserves indexed cached execution whenever
the transitions agree after renaming. Positions and exhaustion are exact. -/

namespace Blotto.CachedWordCursor

def mapState {S T : Type*} (f : S → T) : CachedWordCursor S → CachedWordCursor T
  | .state s => .state (f s)
  | .coin a b hb hab upper lower => .coin a b hb hab (f upper) (f lower)

theorem mapState_ofWords {S T : Type*} (f : S → T) (a b : ℕ) (hb : 0 < b) (hab : a ≤ b) (upper lower : S) :
    (ofWords a b hb hab upper lower).mapState f = ofWords a b hb hab (f upper) (f lower) := rfl

end Blotto.CachedWordCursor
namespace Blotto.WordStateMachine

theorem runCachedIndexed_reindex {S T α : Type*} (m : WordStateMachine S α) (target : WordStateMachine T α)
    (f : S → T) (hStep : ∀ s, target.step (f s) = (m.step s).mapState f)
    (N : ℕ) (bits : Fin N → Bool) (cursor : CachedWordCursor S) (pos : ℕ) (hpos : pos ≤ N) :
    target.runCachedIndexed N bits (cursor.mapState f) pos hpos = m.runCachedIndexed N bits cursor pos hpos := by
  cases cursor with
  | state s =>
    conv_lhs => rw [CachedWordCursor.mapState]; unfold runCachedIndexed
    conv_rhs => unfold runCachedIndexed
    rw [hStep]
    cases hs : m.step s with
    | done value => rfl
    | ask a b hb hab upper lower =>
      have ih := m.runCachedIndexed_reindex target f hStep N bits (.ofWords a b hb hab upper lower) pos hpos
      simpa only [WordTransition.mapState, CachedWordCursor.mapState_ofWords] using ih
  | coin a b hb hab upper lower =>
    conv_lhs => rw [CachedWordCursor.mapState]; unfold runCachedIndexed
    conv_rhs => unfold runCachedIndexed
    by_cases hz : a.isZero = true
    · simp only [dite_eq_left hz]
      exact m.runCachedIndexed_reindex target f hStep N bits (.state lower) pos hpos
    simp only [dite_eq_right hz]
    by_cases he : a.same b = true
    · simp only [dite_eq_left he]
      exact m.runCachedIndexed_reindex target f hStep N bits (.state upper) pos hpos
    simp only [dite_eq_right he]
    by_cases hRead : pos < N
    · simp only [dite_eq_left hRead]
      have hlt : a.value < b.value := lt_of_le_of_ne hab (fun h => he ((a.same_value b).mpr h))
      by_cases hd : bits ⟨pos, hRead⟩ = (a.coinStep b).1
      · simp only [ite_eq_left hd]
        exact m.runCachedIndexed_reindex target f hStep N bits
          (.coin (a.coinStep b).2 b hb (a.coinStep_normalized b hlt).le upper lower) (pos + 1) (by omega)
      · simp only [ite_eq_right hd]
        have ih := m.runCachedIndexed_reindex target f hStep N bits
          (.state (if bits ⟨pos, hRead⟩ then lower else upper)) (pos + 1) (by omega)
        simpa only [CachedWordCursor.mapState, apply_ite] using ih
    · simp only [dite_eq_right hRead]
termination_by (N - pos, m.cachedCursorRank cursor)
decreasing_by
  all_goals simp only [cachedCursorRank]
  · have hp := m.progress s
    rw [hs] at hp
    simp only [CachedWordCursor.ofWords]
    omega
  all_goals omega

theorem runCachedIndexed_state_eq {S α : Type*} (m : WordStateMachine S α) (s t : S)
    (hStep : m.step s = m.step t) (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) :
    m.runCachedIndexed N bits (.state s) pos hpos = m.runCachedIndexed N bits (.state t) pos hpos := by
  conv_lhs => unfold runCachedIndexed
  conv_rhs => unfold runCachedIndexed
  rw [hStep]

end Blotto.WordStateMachine
