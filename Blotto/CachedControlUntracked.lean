import Blotto.CachedControlReindex

/-! An untracked phase contributes no Boolean controller work, while its
actual transitions and coin digits still execute with their original words. -/

namespace Blotto.WordStateMachine

theorem cachedControlWork_untracked {S α : Type*} (m : WordStateMachine S α)
    (tracked : S → Bool) (hTracked : ∀ s, tracked s = false)
    (encodingPrice coinPrice : ℕ → ℕ) (N : ℕ) (bits : Fin N → Bool)
    (cursor : CachedWordCursor S) (pos : ℕ) (hpos : pos ≤ N) :
    m.cachedControlWork tracked encodingPrice coinPrice N bits cursor pos hpos = 0 := by
  cases cursor with
  | state s =>
    conv_lhs => unfold cachedControlWork
    cases hs : m.step s with
    | done value => rfl
    | ask a b hb hab upper lower =>
      simp only [trackedCoin, hTracked, Bool.false_and, Bool.false_eq_true, ite_false, Nat.zero_add]
      exact m.cachedControlWork_untracked tracked hTracked encodingPrice coinPrice N bits
        (.ofWords a b hb hab upper lower) pos hpos
  | @coin w a b hb hab upper lower =>
    conv_lhs => unfold cachedControlWork
    simp only [trackedCoin, hTracked, Bool.false_and, Bool.false_eq_true, ite_false, Nat.zero_add]
    by_cases hz : a.isZero = true
    · simp only [dite_eq_left hz]
      exact m.cachedControlWork_untracked tracked hTracked encodingPrice coinPrice N bits (.state lower) pos hpos
    simp only [dite_eq_right hz]
    by_cases he : a.same b = true
    · simp only [dite_eq_left he]
      exact m.cachedControlWork_untracked tracked hTracked encodingPrice coinPrice N bits (.state upper) pos hpos
    simp only [dite_eq_right he]
    by_cases hRead : pos < N
    · simp only [dite_eq_left hRead]
      have hlt : a.value < b.value := lt_of_le_of_ne hab (fun h => he ((a.same_value b).mpr h))
      by_cases hd : bits ⟨pos, hRead⟩ = (a.coinStep b).1
      · simp only [ite_eq_left hd]
        exact m.cachedControlWork_untracked tracked hTracked encodingPrice coinPrice N bits
          (.coin (a.coinStep b).2 b hb (a.coinStep_normalized b hlt).le upper lower) (pos + 1) (by omega)
      · simp only [ite_eq_right hd]
        have ih := m.cachedControlWork_untracked tracked hTracked encodingPrice coinPrice N bits
          (.state (if bits ⟨pos, hRead⟩ then lower else upper)) (pos + 1) (by omega)
        exact ih
    · simp only [dite_eq_right hRead]
termination_by (N - pos, m.cachedCursorRank cursor)
decreasing_by
  all_goals simp only [cachedCursorRank]
  all_goals first
    | (have hp := m.progress s; rw [hs] at hp; simp only [CachedWordCursor.ofWords]; omega)
    | omega

end Blotto.WordStateMachine
