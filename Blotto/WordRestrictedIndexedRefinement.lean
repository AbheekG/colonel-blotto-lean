import Blotto.WordMachineRestriction
import Blotto.WordMachineRefinement

/-! Erasing invariant/result subtypes preserves every indexed reader path,
including pending coins, failures and the consumed position. Restricted phase
certificates change no transition words or shared-cap behavior. -/
namespace Blotto.WordRestrictedIndexedRefinement

def eraseCursor {S : Type*} (I : S → Prop) : WordCursor {s // I s} → WordCursor S
  | .state s => .state s.val
  | .coin a b hb hab upper lower => .coin a b hb hab upper.val lower.val

def eraseResult {α : Type*} (P : α → Prop) (result : Option {x // P x} × ℕ) : Option α × ℕ :=
  (result.1.map Subtype.val,result.2)

theorem indexed_refines {S α : Type*} (m : WordStateMachine S α) (I : S → Prop) (P : α → Prop)
    (hI : ∀ s, I s → (m.step s).Postcondition I P)
    (N : ℕ) (bits : Fin N → Bool) (cursor : WordCursor {s // I s}) (pos : ℕ) (hpos : pos ≤ N) :
    eraseResult P ((m.restricted I P hI).runCursorIndexed N bits cursor pos hpos) =
      m.runCursorIndexed N bits (eraseCursor I cursor) pos hpos := by
  cases cursor with
  | state s =>
    conv_lhs => unfold WordStateMachine.runCursorIndexed
    conv_rhs => rw [eraseCursor]; unfold WordStateMachine.runCursorIndexed
    cases he : m.step s.val with
    | done x =>
      have hx := hI s.val s.property
      rw [he] at hx
      rw [WordStateMachine.restricted_step,WordTransition.restrict_done I P _ _ x he]
      rfl
    | ask a b hb hab upper lower =>
      rw [WordStateMachine.restricted_step,WordTransition.restrict_ask I P _ _ a b hb hab upper lower he]
      exact indexed_refines m I P hI N bits (.coin a b hb hab _ _) pos hpos
  | coin a b hb hab upper lower =>
    conv_lhs => unfold WordStateMachine.runCursorIndexed
    conv_rhs => rw [eraseCursor]; unfold WordStateMachine.runCursorIndexed
    by_cases hz : a=0
    · simp only [ite_eq_left hz]
      exact indexed_refines m I P hI N bits (.state lower) pos hpos
    · simp only [ite_eq_right hz]
      by_cases hu : b≤a
      · simp only [ite_eq_left hu]
        exact indexed_refines m I P hI N bits (.state upper) pos hpos
      · simp only [ite_eq_right hu]
        by_cases hRead : pos<N
        · simp only [dite_eq_left hRead]
          by_cases hd : bits ⟨pos,hRead⟩=denominatorDigit a b
          · simp only [ite_eq_left hd]
            exact indexed_refines m I P hI N bits
              (.coin (numeratorResidual a b) b hb (numeratorResidual_bounds a b hab) upper lower) (pos+1) (by omega)
          · simp only [ite_eq_right hd]
            have hi := indexed_refines m I P hI N bits
              (.state (if bits ⟨pos,hRead⟩ then lower else upper)) (pos+1) (by omega)
            cases hBit : bits ⟨pos,hRead⟩ <;>
              simpa only [hBit,Bool.false_eq_true,ite_false,ite_true,eraseCursor] using hi
        · simp only [dite_eq_right hRead]
          rfl
termination_by (N-pos,(m.restricted I P hI).cursorRank cursor)
decreasing_by
  all_goals simp only [WordStateMachine.cursorRank,WordStateMachine.restricted]
  · apply Prod.Lex.right
    have hp := m.progress s.val
    rw [he] at hp
    omega
  all_goals try (apply Prod.Lex.right; omega)
  all_goals apply Prod.Lex.left
  all_goals omega

theorem run_refines {S α : Type*} (m : WordStateMachine S α) (I : S → Prop) (P : α → Prop)
    (hI : ∀ s, I s → (m.step s).Postcondition I P) (N : ℕ) (bits : Fin N → Bool) (s : {s // I s}) :
    eraseResult P ((m.restricted I P hI).run N s bits) = m.run N s.val bits := by
  rw [WordStateMachine.run_eq_numeric,WordStateMachine.run_eq_numeric]
  exact indexed_refines m I P hI N bits (.state s) 0 (Nat.zero_le N)

end Blotto.WordRestrictedIndexedRefinement
