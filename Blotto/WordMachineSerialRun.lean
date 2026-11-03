import Blotto.WordMachineRunEmbedding

/-! Sequential indexed execution is exactly serial control flow: the second
machine starts at the first machine's returned position in the same reader.
Both success and exhaustion preserve exact output and final position. -/

namespace Blotto.WordStateMachine

def handoff {α β : Type*} (N : ℕ) (first : Option α × ℕ)
    (next : ∀ _a : α, (pos : ℕ) → pos ≤ N → Option β × ℕ) : Option β × ℕ :=
  match first.1 with
  | none => (none,first.2)
  | some a => if h : first.2 ≤ N then next a first.2 h else (none,first.2)

theorem serial_continuation_run {S α β : Type*} {T : α → Type*} (m : WordStateMachine S α)
    (next : ∀ a, WordStateMachine (T a) β) (start : ∀ a, T a) (C : ℕ)
    (hC : ∀ a, (next a).rank (start a) ≤ C) (a : α) (N : ℕ) (bits : Fin N → Bool)
    (cursor : WordCursor (T a)) (pos : ℕ) (hpos : pos ≤ N) :
    (m.serial next start C hC).runCursorIndexed N bits (cursor.mapState (SerialState.continuation a)) pos hpos =
      (next a).runCursorIndexed N bits cursor pos hpos :=
  embedding_runCursorIndexed (next a) (m.serial next start C hC) (SerialState.continuation a) (fun _ => rfl) N bits cursor pos hpos

theorem serial_source_run {S α β : Type*} {T : α → Type*} (m : WordStateMachine S α)
    (next : ∀ a, WordStateMachine (T a) β) (start : ∀ a, T a) (C : ℕ)
    (hC : ∀ a, (next a).rank (start a) ≤ C) (N : ℕ) (bits : Fin N → Bool)
    (cursor : WordCursor S) (pos : ℕ) (hpos : pos ≤ N) :
    (m.serial next start C hC).runCursorIndexed N bits (cursor.mapState SerialState.source) pos hpos =
      handoff N (m.runCursorIndexed N bits cursor pos hpos)
        (fun a pos hp => (next a).runCursorIndexed N bits (.state (start a)) pos hp) := by
  cases cursor with
  | state s =>
    simp only [WordCursor.mapState]
    conv_lhs => unfold runCursorIndexed
    rw [serial_step]
    simp only [serialTransition]
    conv_rhs => arg 2; unfold runCursorIndexed
    cases hs : m.step s with
    | done a =>
      simp only [handoff,hpos,dite_true]
      have ht := serial_continuation_run m next start C hC a N bits (.state (start a)) pos hpos
      conv_lhs at ht => simp only [WordCursor.mapState]; unfold runCursorIndexed
      rw [serial_step] at ht
      simp only [serialTransition] at ht
      exact ht
    | ask u d hd hud upper lower =>
      change (m.serial next start C hC).runCursorIndexed N bits
        (.coin u d hd hud (.source upper) (.source lower)) pos hpos = _
      exact serial_source_run m next start C hC N bits (.coin u d hd hud upper lower) pos hpos
  | coin u d hd hud upper lower =>
    simp only [WordCursor.mapState]
    conv_lhs => unfold runCursorIndexed
    conv_rhs => arg 2; unfold runCursorIndexed
    by_cases hz : u=0
    · simp only [hz,ite_true]
      exact serial_source_run m next start C hC N bits (.state lower) pos hpos
    · simp only [hz,ite_false]
      by_cases he : d≤u
      · simp only [he,ite_true]
        exact serial_source_run m next start C hC N bits (.state upper) pos hpos
      · simp only [he,ite_false]
        by_cases hRead : pos<N
        · simp only [dite_eq_left hRead]
          by_cases hb : bits ⟨pos,hRead⟩=denominatorDigit u d
          · simp only [hb,ite_true]
            exact serial_source_run m next start C hC N bits
              (.coin (numeratorResidual u d) d hd (numeratorResidual_bounds u d hud) upper lower) (pos+1) (by omega)
          · simp only [hb,ite_false]
            by_cases hBit : bits ⟨pos,hRead⟩=true
            · simp only [hBit,ite_true]
              exact serial_source_run m next start C hC N bits (.state lower) (pos+1) (by omega)
            · simp only [hBit]
              exact serial_source_run m next start C hC N bits (.state upper) (pos+1) (by omega)
        · simp only [dite_eq_right hRead,handoff]
termination_by (N-pos,m.cursorRank cursor)
decreasing_by
  all_goals simp only [cursorRank]
  · have hp := m.progress s
    rw [hs] at hp
    apply Prod.Lex.right
    omega
  all_goals first | (apply Prod.Lex.right; omega) | (apply Prod.Lex.left; omega)

end Blotto.WordStateMachine
