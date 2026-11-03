import Blotto.CachedWordCursor

/-! The cached Boolean controller equals the retained numeric indexed loop
on every cursor and input buffer, including exact position and exhaustion. -/

namespace Blotto.WordStateMachine

theorem runCachedIndexed_refines {S α : Type*} (m : WordStateMachine S α) (N : ℕ)
    (bits : Fin N → Bool) (cursor : CachedWordCursor S) (pos : ℕ) (hpos : pos ≤ N) :
    m.runCachedIndexed N bits cursor pos hpos = m.runCursorIndexed N bits cursor.reference pos hpos := by
  cases cursor with
  | state s =>
    conv_lhs => unfold runCachedIndexed
    conv_rhs => rw [CachedWordCursor.reference]; unfold runCursorIndexed
    cases hs : m.step s with
    | done value => rfl
    | ask a b hb hab upper lower =>
      have h := m.runCachedIndexed_refines N bits (.ofWords a b hb hab upper lower) pos hpos
      simpa only [CachedWordCursor.reference_ofWords] using h
  | coin a b hb hab upper lower =>
    conv_lhs => unfold runCachedIndexed
    conv_rhs => rw [CachedWordCursor.reference]; unfold runCursorIndexed
    have hZero : a.isZero = true ↔ a.value = 0 := a.isZero_value
    have hSame : a.same b = true ↔ b.value ≤ a.value := by
      rw [a.same_value b]
      constructor
      · intro he; rw [he]
      · intro he; exact Nat.le_antisymm hab he
    simp only [hZero, hSame]
    by_cases hz : a.value = 0
    · simp only [dite_eq_left hz, ite_eq_left hz]
      exact m.runCachedIndexed_refines N bits (.state lower) pos hpos
    · simp only [dite_eq_right hz, ite_eq_right hz]
      by_cases he : b.value ≤ a.value
      · simp only [dite_eq_left he, ite_eq_left he]
        exact m.runCachedIndexed_refines N bits (.state upper) pos hpos
      · simp only [dite_eq_right he, ite_eq_right he]
        by_cases hRead : pos < N
        · simp only [dite_eq_left hRead, FixedBinaryWord.coinStep_digit]
          have hlt : a.value < b.value := lt_of_not_ge he
          by_cases hd : bits ⟨pos, hRead⟩ = denominatorDigit a.value b.value
          · simp only [ite_eq_left hd]
            have h := m.runCachedIndexed_refines N bits
              (.coin (a.coinStep b).2 b hb (a.coinStep_normalized b hlt).le upper lower) (pos + 1) (by omega)
            simpa only [CachedWordCursor.reference, a.coinStep_residual b hlt] using h
          · simp only [ite_eq_right hd]
            exact m.runCachedIndexed_refines N bits (.state (if bits ⟨pos, hRead⟩ then lower else upper))
              (pos + 1) (by omega)
        · simp only [dite_eq_right hRead]
termination_by (N - pos, m.cachedCursorRank cursor)
decreasing_by
  all_goals simp only [cachedCursorRank]
  · have hp := m.progress s
    rw [hs] at hp
    simp only [CachedWordCursor.ofWords]
    omega
  all_goals omega

end Blotto.WordStateMachine
