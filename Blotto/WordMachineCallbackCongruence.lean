import Blotto.CachedWordCallbackWork
import Blotto.WordMachineRestriction

/-! Callback prices that agree on a closed reachable-state invariant give
the same total work on every packet/cap. No price condition is imposed on
unreachable states. Pending coins preserve both successor invariants. -/

namespace Blotto.WordStateMachine

def cursorInvariant {S : Type*} (I : S → Prop) : WordCursor S → Prop
  | .state s => I s
  | .coin _ _ _ _ upper lower => I upper ∧ I lower

theorem indexedCallbackWork_congr {S α : Type*} (m : WordStateMachine S α) (I : S → Prop)
    (left right : S → ℕ) (hEq : ∀ s, I s → left s = right s)
    (hClosed : ∀ s, I s → (m.step s).Postcondition I (fun _ => True))
    (N : ℕ) (bits : Fin N → Bool) (cursor : WordCursor S) (pos : ℕ) (hpos : pos ≤ N)
    (hI : cursorInvariant I cursor) :
    m.indexedCallbackWork left N bits cursor pos hpos = m.indexedCallbackWork right N bits cursor pos hpos := by
  cases hCursorEq : cursor with
  | state s =>
    rw [hCursorEq] at hI
    change I s at hI
    have hp := hClosed s hI
    have he := hEq s hI
    conv_lhs => unfold indexedCallbackWork
    conv_rhs => unfold indexedCallbackWork
    rw [he]
    cases ht : m.step s with
    | done value => rfl
    | ask a b hb hab upper lower =>
      rw [ht] at hp
      exact congrArg (fun w => right s + w)
        (m.indexedCallbackWork_congr I left right hEq hClosed N bits (.coin a b hb hab upper lower) pos hpos hp)
  | coin a b hb hab upper lower =>
    rw [hCursorEq] at hI
    change I upper ∧ I lower at hI
    conv_lhs => unfold indexedCallbackWork
    conv_rhs => unfold indexedCallbackWork
    by_cases ha : a = 0
    · simp only [ha, ite_true]
      exact m.indexedCallbackWork_congr I left right hEq hClosed N bits (.state lower) pos hpos hI.2
    by_cases hba : b ≤ a
    · simp only [ha, hba, ite_false, ite_true]
      exact m.indexedCallbackWork_congr I left right hEq hClosed N bits (.state upper) pos hpos hI.1
    simp only [ha, hba, ite_false]
    by_cases hRead : pos < N
    · simp only [dite_eq_left hRead]
      by_cases hd : bits ⟨pos, hRead⟩ = denominatorDigit a b
      · simp only [hd, ite_true]
        exact m.indexedCallbackWork_congr I left right hEq hClosed N bits
          (.coin (numeratorResidual a b) b hb (numeratorResidual_bounds a b hab) upper lower) (pos + 1) (by omega) hI
      · simp only [hd, ite_false]
        exact m.indexedCallbackWork_congr I left right hEq hClosed N bits
          (.state (if bits ⟨pos, hRead⟩ then lower else upper)) (pos + 1) (by omega)
          (by
            change I (if bits ⟨pos, hRead⟩ then lower else upper)
            split_ifs
            · exact hI.2
            · exact hI.1)
    · simp only [dite_eq_right hRead]
termination_by (N - pos, m.cursorRank cursor)
decreasing_by
  all_goals simp only [hCursorEq, cursorRank]
  · have hp := m.progress s
    rw [ht] at hp
    omega
  all_goals omega

theorem runCachedCallbackWork_congr {S α : Type*} (m : WordStateMachine S α) (I : S → Prop)
    (left right : S → ℕ) (hEq : ∀ s, I s → left s = right s)
    (hClosed : ∀ s, I s → (m.step s).Postcondition I (fun _ => True))
    (R : ℕ) (s : S) (hI : I s) (bits : Fin R → Bool) :
    m.runCachedCallbackWork left R s bits = m.runCachedCallbackWork right R s bits := by
  rw [m.runCachedCallbackWork_eq, m.runCachedCallbackWork_eq]
  exact m.indexedCallbackWork_congr I left right hEq hClosed R bits (.state s) 0 (Nat.zero_le _) hI

end Blotto.WordStateMachine
