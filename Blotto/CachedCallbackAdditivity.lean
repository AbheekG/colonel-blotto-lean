import Blotto.CachedWordCallbackWork

/-! Arbitrary callback price ledgers add on one indexed control path, including
zero/one coins and cap exhaustion. No extra runtime traversal is introduced. -/

namespace Blotto.WordStateMachine

theorem cachedCallbackWork_add {S α : Type*} (m : WordStateMachine S α) (left right : S → ℕ)
    (N : ℕ) (bits : Fin N → Bool) (cursor : CachedWordCursor S) (pos : ℕ) (hpos : pos ≤ N) :
    m.cachedCallbackWork (fun s => left s + right s) N bits cursor pos hpos =
      m.cachedCallbackWork left N bits cursor pos hpos + m.cachedCallbackWork right N bits cursor pos hpos := by
  cases cursor with
  | state s =>
    conv_lhs => unfold cachedCallbackWork
    conv_rhs =>
      lhs
      unfold cachedCallbackWork
    conv_rhs =>
      rhs
      unfold cachedCallbackWork
    cases hs : m.step s with
    | done value => rfl
    | ask a b hb hab upper lower =>
      dsimp only
      have ih := m.cachedCallbackWork_add left right N bits (.ofWords a b hb hab upper lower) pos hpos
      omega
  | coin a b hb hab upper lower =>
    conv_lhs => unfold cachedCallbackWork
    conv_rhs =>
      lhs
      unfold cachedCallbackWork
    conv_rhs =>
      rhs
      unfold cachedCallbackWork
    by_cases hz : a.isZero = true
    · simp only [dite_eq_left hz]
      have ih := m.cachedCallbackWork_add left right N bits (.state lower) pos hpos
      omega
    simp only [dite_eq_right hz]
    by_cases he : a.same b = true
    · simp only [dite_eq_left he]
      have ih := m.cachedCallbackWork_add left right N bits (.state upper) pos hpos
      omega
    simp only [dite_eq_right he]
    by_cases hRead : pos < N
    · simp only [dite_eq_left hRead]
      have hlt : a.value < b.value := lt_of_le_of_ne hab (fun h => he ((a.same_value b).mpr h))
      by_cases hd : bits ⟨pos, hRead⟩ = (a.coinStep b).1
      · simp only [ite_eq_left hd]
        have ih := m.cachedCallbackWork_add left right N bits
          (.coin (a.coinStep b).2 b hb (a.coinStep_normalized b hlt).le upper lower) (pos + 1) (by omega)
        omega
      · simp only [ite_eq_right hd]
        have ih := m.cachedCallbackWork_add left right N bits
          (.state (if bits ⟨pos, hRead⟩ then lower else upper)) (pos + 1) (by omega)
        omega
    · simp only [dite_eq_right hRead]
termination_by (N - pos, m.cachedCursorRank cursor)
decreasing_by
  all_goals simp only [cachedCursorRank]
  all_goals first
    | (have hp := m.progress s; rw [hs] at hp; simp only [CachedWordCursor.ofWords]; omega)
    | omega

end Blotto.WordStateMachine
