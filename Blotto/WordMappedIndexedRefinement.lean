import Blotto.WordMachineMap
import Blotto.WordMachineRefinement

/-! Mapping a word machine's output leaves every indexed cursor, coin digit,
exhaustion decision and consumed position unchanged. This result maps only the
successful Option payload. It supplies exact categorical-slot-to-allocation
callback refinement without constructing any source choice tree. -/
namespace Blotto.WordMappedIndexedRefinement

def mapResult {α β : Type*} (f : α → β) (result : Option α × ℕ) : Option β × ℕ :=
  (result.1.map f,result.2)

theorem indexed_refines {S α β : Type*} (m : WordStateMachine S α) (f : α → β)
    (N : ℕ) (bits : Fin N → Bool) (cursor : WordCursor S) (pos : ℕ) (hpos : pos ≤ N) :
    (m.mapped f).runCursorIndexed N bits cursor pos hpos = mapResult f (m.runCursorIndexed N bits cursor pos hpos) := by
  cases cursor with
  | state s =>
    conv_lhs => unfold WordStateMachine.runCursorIndexed
    conv_rhs => unfold WordStateMachine.runCursorIndexed
    rw [WordStateMachine.mapped_step]
    cases he : m.step s with
    | done value => rfl
    | ask a b hb hab upper lower =>
      exact indexed_refines m f N bits (.coin a b hb hab upper lower) pos hpos
  | coin a b hb hab upper lower =>
    conv_lhs => unfold WordStateMachine.runCursorIndexed
    conv_rhs => unfold WordStateMachine.runCursorIndexed
    by_cases hz : a=0
    · simp only [ite_eq_left hz]
      exact indexed_refines m f N bits (.state lower) pos hpos
    · simp only [ite_eq_right hz]
      by_cases hu : b≤a
      · simp only [ite_eq_left hu]
        exact indexed_refines m f N bits (.state upper) pos hpos
      · simp only [ite_eq_right hu]
        by_cases hRead : pos<N
        · simp only [dite_eq_left hRead]
          by_cases hd : bits ⟨pos,hRead⟩=denominatorDigit a b
          · simp only [ite_eq_left hd]
            exact indexed_refines m f N bits
              (.coin (numeratorResidual a b) b hb (numeratorResidual_bounds a b hab) upper lower) (pos+1) (by omega)
          · simp only [ite_eq_right hd]
            exact indexed_refines m f N bits (.state (if bits ⟨pos,hRead⟩ then lower else upper)) (pos+1) (by omega)
        · simp only [dite_eq_right hRead]
          rfl
termination_by (N-pos,m.cursorRank cursor)
decreasing_by
  all_goals simp only [WordStateMachine.cursorRank]
  · apply Prod.Lex.right
    have hp := m.progress s
    rw [he] at hp
    omega
  all_goals try (apply Prod.Lex.right; omega)
  all_goals apply Prod.Lex.left
  all_goals omega

theorem run_refines {S α β : Type*} (m : WordStateMachine S α) (f : α → β)
    (N : ℕ) (s : S) (bits : Fin N → Bool) :
    (m.mapped f).run N s bits = mapResult f (m.run N s bits) := by
  rw [WordStateMachine.run_eq_numeric,WordStateMachine.run_eq_numeric]
  exact indexed_refines m f N bits (.state s) 0 (Nat.zero_le N)

theorem indexed_position {S α β : Type*} (m : WordStateMachine S α) (f : α → β)
    (N : ℕ) (bits : Fin N → Bool) (cursor : WordCursor S) (pos : ℕ) (hpos : pos ≤ N) :
    ((m.mapped f).runCursorIndexed N bits cursor pos hpos).2 = (m.runCursorIndexed N bits cursor pos hpos).2 :=
  congrArg Prod.snd (indexed_refines m f N bits cursor pos hpos)

theorem indexed_failure_iff {S α β : Type*} (m : WordStateMachine S α) (f : α → β)
    (N : ℕ) (bits : Fin N → Bool) (cursor : WordCursor S) (pos : ℕ) (hpos : pos ≤ N) :
    ((m.mapped f).runCursorIndexed N bits cursor pos hpos).1=none ↔
      (m.runCursorIndexed N bits cursor pos hpos).1=none := by
  rw [indexed_refines,mapResult]
  exact Option.map_eq_none_iff

theorem indexed_success {S α β : Type*} (m : WordStateMachine S α) (f : α → β)
    (N : ℕ) (bits : Fin N → Bool) (cursor : WordCursor S) (pos : ℕ) (hpos : pos ≤ N) (value : α)
    (h : (m.runCursorIndexed N bits cursor pos hpos).1=some value) :
    ((m.mapped f).runCursorIndexed N bits cursor pos hpos).1=some (f value) := by
  rw [indexed_refines,mapResult,h,Option.map_some]

end Blotto.WordMappedIndexedRefinement
