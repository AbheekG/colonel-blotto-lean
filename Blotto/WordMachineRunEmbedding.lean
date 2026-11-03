import Blotto.WordMachineEmbedding
import Blotto.WordMachineIndexedRefinement

/-! Transition-preserving embeddings retain exact indexed results and global
reader positions, including pending coins and exhaustion. No input windows or
proof choice trees are created by execution. -/

namespace Blotto
namespace WordCursor

def mapState {S T : Type*} (embed : S → T) : WordCursor S → WordCursor T
  | .state s => .state (embed s)
  | .coin a b hb hab upper lower => .coin a b hb hab (embed upper) (embed lower)

end WordCursor
namespace WordStateMachine

theorem embedding_runCursorIndexed {S T α : Type*} (first : WordStateMachine S α) (second : WordStateMachine T α)
    (embed : S → T) (h : ∀ s, second.step (embed s) = (first.step s).mapState embed)
    (N : ℕ) (bits : Fin N → Bool) (cursor : WordCursor S) (pos : ℕ) (hpos : pos ≤ N) :
    second.runCursorIndexed N bits (cursor.mapState embed) pos hpos = first.runCursorIndexed N bits cursor pos hpos := by
  cases cursor with
  | state s =>
    simp only [WordCursor.mapState]
    conv_lhs => unfold runCursorIndexed
    conv_rhs => unfold runCursorIndexed
    rw [h]
    cases hs : first.step s with
    | done value => rfl
    | ask a b hb hab upper lower =>
      exact embedding_runCursorIndexed first second embed h N bits (.coin a b hb hab upper lower) pos hpos
  | coin a b hb hab upper lower =>
    simp only [WordCursor.mapState]
    conv_lhs => unfold runCursorIndexed
    conv_rhs => unfold runCursorIndexed
    by_cases hz : a=0
    · simp only [hz,ite_true]
      exact embedding_runCursorIndexed first second embed h N bits (.state lower) pos hpos
    · simp only [hz,ite_false]
      by_cases he : b≤a
      · simp only [he,ite_true]
        exact embedding_runCursorIndexed first second embed h N bits (.state upper) pos hpos
      · simp only [he,ite_false]
        by_cases hRead : pos<N
        · simp only [dite_eq_left hRead]
          by_cases hd : bits ⟨pos,hRead⟩=denominatorDigit a b
          · simp only [hd,ite_true]
            exact embedding_runCursorIndexed first second embed h N bits
              (.coin (numeratorResidual a b) b hb (numeratorResidual_bounds a b hab) upper lower) (pos+1) (by omega)
          · simp only [hd,ite_false]
            cases hBit : bits ⟨pos,hRead⟩
            · simp only [Bool.false_eq_true,ite_false]
              exact embedding_runCursorIndexed first second embed h N bits (.state upper) (pos+1) (by omega)
            · simp only [ite_true]
              exact embedding_runCursorIndexed first second embed h N bits (.state lower) (pos+1) (by omega)
        · simp only [dite_eq_right hRead]
termination_by (N-pos,first.cursorRank cursor)
decreasing_by
  all_goals simp only [cursorRank]
  · have hp := first.progress s
    rw [hs] at hp
    apply Prod.Lex.right
    omega
  · apply Prod.Lex.right; omega
  · apply Prod.Lex.right; omega
  all_goals apply Prod.Lex.left
  all_goals omega

theorem runCursorIndexed_position_bounds {S α : Type*} (m : WordStateMachine S α) (N : ℕ) (bits : Fin N → Bool)
    (cursor : WordCursor S) (pos : ℕ) (hpos : pos ≤ N) :
    pos ≤ (m.runCursorIndexed N bits cursor pos hpos).2 ∧ (m.runCursorIndexed N bits cursor pos hpos).2 ≤ N := by
  rw [m.runCursorIndexed_window N bits cursor pos (N-pos) (by omega)]
  have hb := (m.cursorSpecification cursor).sample_bits_le (N-pos) (inputWindow bits pos (N-pos) (by omega))
  rw [← m.runCursor_refines] at hb
  simp only [offsetConsumed]
  omega

end WordStateMachine
end Blotto
