import Blotto.SharedResourceLattice
import Blotto.RationalLottoSharedRun

/-! Terminal work is delegated at the actual primary source-completion
position. The same reader/cap is retained. A remaining-bit linear allowance
does not grow during prefix traversal; source exhaustion pays zero. -/

namespace Blotto.RationalLottoResourceSystem

noncomputable def sharedTerminalWindowWork {n : ℕ} (i : RationalLottoResourceSystem n) (N : ℕ) (bits : Fin N → Bool)
    (terminalWork : i.PhaseResult → (pos : ℕ) → pos ≤ N → ℕ)
    (cursor : SharedResourceCursor i.length) (hCursor : i.SharedInvariant cursor) (pos : ℕ) (hpos : pos ≤ N) : ℕ :=
  match cursor with
  | .ready state => match hp : prepareResourceChoice state with
    | .done value => terminalWork ⟨value, i.shared_done_terminal state hCursor value hp⟩ pos hpos
    | .ask p => i.sharedTerminalWindowWork N bits terminalWork (SharedResourceCursor.prepared p)
        (i.shared_prepared_invariant state hCursor p hp) pos hpos
  | .coin choice a b hb hab =>
    if hz : a.isZero = true then i.sharedTerminalWindowWork N bits terminalWork
        (.ready (choice.select false)) (i.choice_select_invariant choice hCursor false) pos hpos else
      if he : a.same b = true then i.sharedTerminalWindowWork N bits terminalWork
        (.ready (choice.select true)) (i.choice_select_invariant choice hCursor true) pos hpos else
        if hRead : pos < N then
          let next := a.coinStep b
          have hlt : a.value < b.value := lt_of_le_of_ne hab (fun h => he ((a.same_value b).mpr h))
          if bits ⟨pos, hRead⟩ = next.1 then
            i.sharedTerminalWindowWork N bits terminalWork
              (.coin choice next.2 b hb (a.coinStep_normalized b hlt).le) hCursor (pos + 1) (by omega)
          else i.sharedTerminalWindowWork N bits terminalWork (.ready (choice.select (!bits ⟨pos, hRead⟩)))
            (i.choice_select_invariant choice hCursor (!bits ⟨pos, hRead⟩)) (pos + 1) (by omega)
        else 0
termination_by (N - pos, cursor.rank)
decreasing_by
  · apply Prod.Lex.right
    exact SharedResourceCursor.prepared_rank_lt state p hp
  · apply Prod.Lex.right
    exact SharedResourceCursor.selected_rank_lt choice a b hb hab false
  · apply Prod.Lex.right
    exact SharedResourceCursor.selected_rank_lt choice a b hb hab true
  all_goals apply Prod.Lex.left
  all_goals omega

theorem sharedTerminalWindowWork_bound {n : ℕ} (i : RationalLottoResourceSystem n) (D : ℕ)
    (hL : ∀ j, OnRationalLattice D (i.length j)) (N : ℕ) (bits : Fin N → Bool)
    (terminalWork : i.PhaseResult → (pos : ℕ) → pos ≤ N → ℕ) (A B : ℕ)
    (hTerminal : ∀ value, value.1.resource.OnLattice D → ∀ pos hpos, terminalWork value pos hpos ≤ A + B * (N - pos))
    (cursor : SharedResourceCursor i.length) (hCursor : i.SharedInvariant cursor) (hLat : cursor.OnLattice D)
    (pos : ℕ) (hpos : pos ≤ N) : i.sharedTerminalWindowWork N bits terminalWork cursor hCursor pos hpos ≤ A + B * (N - pos) := by
  revert hCursor hLat
  cases hCursorEq : cursor with
  | ready state =>
    intro hCursor hLat
    conv_lhs => unfold sharedTerminalWindowWork
    split
    · rename_i value hp
      exact hTerminal ⟨value, i.shared_done_terminal state hCursor value hp⟩
        (SharedResourceCursor.done_on_lattice D hL state hLat value hp) pos hpos
    · rename_i p hp
      exact i.sharedTerminalWindowWork_bound D hL N bits terminalWork A B hTerminal (SharedResourceCursor.prepared p)
        (i.shared_prepared_invariant state hCursor p hp) (SharedResourceCursor.prepared_on_lattice D state hLat p hp) pos hpos
  | coin choice a b hb hab =>
    intro hCursor hLat
    conv_lhs => unfold sharedTerminalWindowWork
    by_cases hz : a.isZero = true
    · simp only [dite_eq_left hz]
      exact i.sharedTerminalWindowWork_bound D hL N bits terminalWork A B hTerminal (.ready (choice.select false))
        (i.choice_select_invariant choice hCursor false) (choice.select_on_lattice D hL hLat false) pos hpos
    · simp only [dite_eq_right hz]
      by_cases he : a.same b = true
      · simp only [dite_eq_left he]
        exact i.sharedTerminalWindowWork_bound D hL N bits terminalWork A B hTerminal (.ready (choice.select true))
          (i.choice_select_invariant choice hCursor true) (choice.select_on_lattice D hL hLat true) pos hpos
      · simp only [dite_eq_right he]
        by_cases hRead : pos < N
        · simp only [dite_eq_left hRead]
          by_cases hd : bits ⟨pos, hRead⟩ = (a.coinStep b).1
          · simp only [ite_eq_left hd]
            have hlt : a.value < b.value := lt_of_le_of_ne hab (fun h => he ((a.same_value b).mpr h))
            have hp := i.sharedTerminalWindowWork_bound D hL N bits terminalWork A B hTerminal
              (.coin choice (a.coinStep b).2 b hb (a.coinStep_normalized b hlt).le) hCursor hLat (pos + 1) (by omega)
            exact hp.trans (Nat.add_le_add_left (Nat.mul_le_mul_left B (by omega)) A)
          · simp only [ite_eq_right hd]
            have hp := i.sharedTerminalWindowWork_bound D hL N bits terminalWork A B hTerminal
              (.ready (choice.select (!bits ⟨pos, hRead⟩))) (i.choice_select_invariant choice hCursor (!bits ⟨pos, hRead⟩))
              (choice.select_on_lattice D hL hLat _) (pos + 1) (by omega)
            exact hp.trans (Nat.add_le_add_left (Nat.mul_le_mul_left B (by omega)) A)
        · simp only [dite_eq_right hRead, Nat.zero_le]
termination_by (N - pos, cursor.rank)
decreasing_by
  all_goals simp only [hCursorEq]
  all_goals first
    | (apply Prod.Lex.right; apply SharedResourceCursor.prepared_rank_lt; assumption)
    | (apply Prod.Lex.right; exact SharedResourceCursor.selected_rank_lt choice a b hb hab false)
    | (apply Prod.Lex.right; exact SharedResourceCursor.selected_rank_lt choice a b hb hab true)
    | (apply Prod.Lex.left; omega)

end Blotto.RationalLottoResourceSystem
