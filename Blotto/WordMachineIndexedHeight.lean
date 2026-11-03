import Blotto.WordMachineRunHeight

/-! Operand certificates follow the primary indexed loop directly, including
every visited state, pending fixed-denominator digit and exhausted cap. -/

namespace Blotto.WordStateMachine

def IndexedWordsBounded {S α : Type*} (m : WordStateMachine S α) (I : S → Prop) (w N : ℕ)
    (bits : Fin N → Bool) (cursor : WordCursor S) (pos : ℕ) (hpos : pos ≤ N) : Prop :=
  match cursor with
  | .state s =>
    I s ∧ match _hs : m.step s with
    | .done _ => True
    | .ask a b hb hab upper lower => m.IndexedWordsBounded I w N bits (.coin a b hb hab upper lower) pos hpos
  | .coin a b hb hab upper lower =>
    (a < 2 ^ w ∧ b < 2 ^ w) ∧ 2 * a < 2 ^ (w + 1) ∧
      if a = 0 then m.IndexedWordsBounded I w N bits (.state lower) pos hpos else
      if b ≤ a then m.IndexedWordsBounded I w N bits (.state upper) pos hpos else
        if hRead : pos < N then
          let bit := bits ⟨pos, hRead⟩
          if bit = denominatorDigit a b then
            m.IndexedWordsBounded I w N bits
              (.coin (numeratorResidual a b) b hb (numeratorResidual_bounds a b hab) upper lower) (pos + 1) (by omega)
          else m.IndexedWordsBounded I w N bits (.state (if bit then lower else upper)) (pos + 1) (by omega)
        else True
termination_by (N - pos, m.cursorRank cursor)
decreasing_by
  all_goals simp_wf
  all_goals simp only [cursorRank]
  · have hp := m.progress s
    rw [_hs] at hp
    omega
  all_goals omega

theorem runCursorIndexed_wordsBounded {S α : Type*} (m : WordStateMachine S α) (I : S → Prop) (w : ℕ)
    (hWords : ∀ s, I s → (m.step s).WordsHeight w)
    (hClosed : ∀ s, I s → (m.step s).Postcondition I (fun _ => True))
    (N : ℕ) (bits : Fin N → Bool) (cursor : WordCursor S) (pos : ℕ) (hpos : pos ≤ N)
    (hCursor : cursor.Bounded I w) : m.IndexedWordsBounded I w N bits cursor pos hpos := by
  cases hCursorEq : cursor with
  | state s =>
    rw [hCursorEq] at hCursor
    unfold IndexedWordsBounded
    refine ⟨hCursor, ?_⟩
    cases ht : m.step s with
    | done x => trivial
    | ask a b hb hab upper lower =>
      have hw := hWords s hCursor
      have hc := hClosed s hCursor
      rw [ht] at hw hc
      exact m.runCursorIndexed_wordsBounded I w hWords hClosed N bits
        (.coin a b hb hab upper lower) pos hpos ⟨hw, hc⟩
  | coin a b hb hab upper lower =>
    rw [hCursorEq] at hCursor
    unfold IndexedWordsBounded
    refine ⟨hCursor.1, coin_doubling_height a w hCursor.1.1, ?_⟩
    by_cases ha : a = 0
    · rw [ite_eq_left ha]
      exact m.runCursorIndexed_wordsBounded I w hWords hClosed N bits (.state lower) pos hpos hCursor.2.2
    rw [ite_eq_right ha]
    by_cases hba : b ≤ a
    · rw [ite_eq_left hba]
      exact m.runCursorIndexed_wordsBounded I w hWords hClosed N bits (.state upper) pos hpos hCursor.2.1
    rw [ite_eq_right hba]
    by_cases hRead : pos < N
    · rw [dite_eq_left hRead]
      by_cases hd : bits ⟨pos, hRead⟩ = denominatorDigit a b
      · rw [ite_eq_left hd]
        exact m.runCursorIndexed_wordsBounded I w hWords hClosed N bits
          (.coin (numeratorResidual a b) b hb (numeratorResidual_bounds a b hab) upper lower)
          (pos + 1) (by omega) ⟨⟨coin_residual_height a b w hab hCursor.1.2, hCursor.1.2⟩, hCursor.2⟩
      · rw [ite_eq_right hd]
        apply m.runCursorIndexed_wordsBounded I w hWords hClosed N bits _ (pos + 1) (by omega)
        by_cases hbit : bits ⟨pos, hRead⟩ = true
        · simpa [hbit, WordCursor.Bounded] using hCursor.2.2
        · simpa [hbit, WordCursor.Bounded] using hCursor.2.1
    · rw [dite_eq_right hRead]
      trivial
termination_by (N - pos, m.cursorRank cursor)
decreasing_by
  all_goals simp only [hCursorEq, cursorRank]
  · have hp := m.progress s
    rw [ht] at hp
    omega
  all_goals omega

end Blotto.WordStateMachine
