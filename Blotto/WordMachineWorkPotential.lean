import Blotto.WordMachineCallbackWork

/-! A telescoping work potential bounds selected callback work without
multiplying a one-time preparation price by the total callback count. Pending
coin digits preserve the potential; exhaustion adds no further work. -/

namespace Blotto.WordStateMachine

def WorkPotential {S α : Type*} (m : WordStateMachine S α) (charge potential : S → ℕ) : Prop :=
  ∀ s, match m.step s with
    | .done _ => charge s ≤ potential s
    | .ask _ _ _ _ upper lower =>
      charge s + potential upper ≤ potential s ∧ charge s + potential lower ≤ potential s

def cursorPotential {S : Type*} (potential : S → ℕ) : WordCursor S → ℕ
  | .state s => potential s
  | .coin _ _ _ _ upper lower => max (potential upper) (potential lower)

theorem indexedCallbackWork_potential {S α : Type*} (m : WordStateMachine S α)
    (charge potential : S → ℕ) (hCost : m.WorkPotential charge potential)
    (N : ℕ) (bits : Fin N → Bool) (cursor : WordCursor S) (pos : ℕ) (hpos : pos ≤ N) :
    m.indexedCallbackWork charge N bits cursor pos hpos ≤ cursorPotential potential cursor := by
  cases cursor with
  | state s =>
    conv_lhs => unfold indexedCallbackWork
    have hp := hCost s
    cases ht : m.step s with
    | done value =>
      rw [ht] at hp
      simpa only [Nat.add_zero, cursorPotential] using hp
    | ask a b hb hab upper lower =>
      rw [ht] at hp
      have hr := m.indexedCallbackWork_potential charge potential hCost N bits
        (.coin a b hb hab upper lower) pos hpos
      have hm : charge s + max (potential upper) (potential lower) ≤ potential s := by omega
      simp only [cursorPotential] at hr ⊢
      omega
  | coin a b hb hab upper lower =>
    conv_lhs => unfold indexedCallbackWork
    by_cases ha : a = 0
    · simp only [ha, ite_true, cursorPotential]
      exact (m.indexedCallbackWork_potential charge potential hCost N bits (.state lower) pos hpos).trans (le_max_right _ _)
    by_cases hba : b ≤ a
    · simp only [ha, hba, ite_false, ite_true, cursorPotential]
      exact (m.indexedCallbackWork_potential charge potential hCost N bits (.state upper) pos hpos).trans (le_max_left _ _)
    simp only [ha, hba, ite_false]
    by_cases hRead : pos < N
    · simp only [dite_eq_left hRead]
      by_cases hd : bits ⟨pos, hRead⟩ = denominatorDigit a b
      · simp only [hd, ite_true]
        exact m.indexedCallbackWork_potential charge potential hCost N bits
          (.coin (numeratorResidual a b) b hb (numeratorResidual_bounds a b hab) upper lower) (pos + 1) (by omega)
      · simp only [hd, ite_false, cursorPotential]
        have hr := m.indexedCallbackWork_potential charge potential hCost N bits
          (.state (if bits ⟨pos, hRead⟩ then lower else upper)) (pos + 1) (by omega)
        simp only [cursorPotential] at hr
        exact hr.trans (by
          split_ifs
          · exact le_max_right _ _
          · exact le_max_left _ _)
    · simp only [dite_eq_right hRead]
      exact Nat.zero_le _
termination_by (N - pos, m.cursorRank cursor)
decreasing_by
  all_goals simp only [cursorRank]
  · have hp := m.progress s
    rw [ht] at hp
    omega
  all_goals omega

theorem runCallbackWork_potential {S α : Type*} (m : WordStateMachine S α)
    (charge potential : S → ℕ) (hCost : m.WorkPotential charge potential)
    (R : ℕ) (s : S) (bits : Fin R → Bool) : m.runCallbackWork charge R s bits ≤ potential s :=
  m.indexedCallbackWork_potential charge potential hCost R bits (.state s) 0 (Nat.zero_le R)

end Blotto.WordStateMachine
