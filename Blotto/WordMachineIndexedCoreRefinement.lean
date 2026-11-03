import Blotto.WordStateMachineCore

/-! The single-buffer indexed tail interpreter equals the original cursor
interpreter for every window, including exact consumed counts and exhaustion.
Window functions occur only in this proof interface, never in the new loop. -/

namespace Blotto.WordStateMachine

theorem inputWindow_head {N : ℕ} (bits : Fin N → Bool) (pos length : ℕ) (h : pos + (length + 1) ≤ N) :
    inputWindow bits pos (length + 1) h 0 = bits ⟨pos, by omega⟩ := by
  simp [inputWindow]

theorem inputWindow_tail {N : ℕ} (bits : Fin N → Bool) (pos length : ℕ) (h : pos + (length + 1) ≤ N) :
    Fin.tail (inputWindow bits pos (length + 1) h) = inputWindow bits (pos + 1) length (by omega) := by
  funext j
  change bits ⟨pos + (j.val + 1), by omega⟩ = bits ⟨pos + 1 + j.val, by omega⟩
  congr 1
  apply Fin.ext
  change pos + (j.val + 1) = pos + 1 + j.val
  omega

theorem inputWindow_zero {N : ℕ} (bits : Fin N → Bool) : inputWindow bits 0 N (by omega) = bits := by
  funext j
  unfold inputWindow
  congr 1
  apply Fin.ext
  simp

theorem offsetConsumed_step {α : Type*} (pos : ℕ) (result : Option α × ℕ) :
    offsetConsumed pos (result.1, result.2 + 1) = offsetConsumed (pos + 1) result := by
  simp only [offsetConsumed]
  congr 1
  omega

theorem runCursorIndexed_window {S α : Type*} (m : WordStateMachine S α) (N : ℕ) (bits : Fin N → Bool)
    (cursor : WordCursor S) (pos length : ℕ) (h : pos + length = N) :
    m.runCursorIndexed N bits cursor pos (by omega) =
      offsetConsumed pos (m.runCursor length cursor (inputWindow bits pos length (by omega))) := by
  cases cursor with
  | state s =>
    conv_lhs => unfold runCursorIndexed
    conv_rhs => unfold runCursor
    cases ht : m.step s with
    | done value => simp only [offsetConsumed, Nat.add_zero]
    | ask a b hb hab upper lower =>
      exact m.runCursorIndexed_window N bits (.coin a b hb hab upper lower) pos length h
  | coin a b hb hab upper lower =>
    conv_lhs => unfold runCursorIndexed
    conv_rhs => unfold runCursor
    by_cases ha : a = 0
    · simp only [ha, ite_true]
      exact m.runCursorIndexed_window N bits (.state lower) pos length h
    by_cases hba : b ≤ a
    · simp only [ha, hba, ite_false, ite_true]
      exact m.runCursorIndexed_window N bits (.state upper) pos length h
    simp only [ha, hba, ite_false]
    cases length with
    | zero =>
      have hN : pos = N := by omega
      simp only [hN, lt_self_iff_false, dite_false, offsetConsumed, Nat.add_zero]
    | succ length =>
      have hRead : pos < N := by omega
      rw [dite_eq_left hRead]
      dsimp only
      rw [inputWindow_head]
      by_cases hd : bits ⟨pos, hRead⟩ = denominatorDigit a b
      · simp only [hd, ite_true]
        rw [inputWindow_tail, offsetConsumed_step]
        exact m.runCursorIndexed_window N bits
          (.coin (numeratorResidual a b) b hb (numeratorResidual_bounds a b hab) upper lower) (pos + 1) length (by omega)
      · simp only [hd, ite_false]
        rw [inputWindow_tail, offsetConsumed_step]
        exact m.runCursorIndexed_window N bits (.state (if bits ⟨pos, hRead⟩ then lower else upper))
          (pos + 1) length (by omega)
termination_by (length, m.cursorRank cursor)
decreasing_by
  all_goals simp only [cursorRank]
  · have hp := m.progress s
    rw [ht] at hp
    omega
  all_goals omega

theorem runCursorIndexed_zero {S α : Type*} (m : WordStateMachine S α) (R : ℕ) (cursor : WordCursor S)
    (bits : Fin R → Bool) : m.runCursorIndexed R bits cursor 0 (Nat.zero_le R) = m.runCursor R cursor bits := by
  have h := m.runCursorIndexed_window R bits cursor 0 R (by omega)
  simpa only [inputWindow_zero, offsetConsumed, Nat.zero_add, Prod.mk.eta] using h

end Blotto.WordStateMachine
