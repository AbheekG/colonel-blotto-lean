import Blotto.RationalLottoSharedRun

/-! The primary one-state source loop accepts an explicit terminal compiler.
Its reader, positions, source transitions and cap remain the original ones.
Equivalent terminal programs preserve the complete execution result. -/

namespace Blotto.RationalLottoResourceSystem

def runSharedWithTerminalIndexed {n : ℕ} (i : RationalLottoResourceSystem n)
    (terminalProgram : i.PhaseResult → RationalAllocationProgram n 80)
    (N : ℕ) (bits : Fin N → Bool) (cursor : SharedResourceCursor i.length) (hCursor : i.SharedInvariant cursor)
    (pos : ℕ) (hpos : pos ≤ N) : Option (Fin n → ℚ) × ℕ :=
  match cursor with
  | .ready state => match hp : prepareResourceChoice state with
    | .done value =>
      let terminal : i.PhaseResult := ⟨value, i.shared_done_terminal state hCursor value hp⟩
      let program := terminalProgram terminal
      program.machine.runCachedIndexed N bits (.state program.start) pos hpos
    | .ask p => i.runSharedWithTerminalIndexed terminalProgram N bits (SharedResourceCursor.prepared p)
        (i.shared_prepared_invariant state hCursor p hp) pos hpos
  | .coin choice a b hb hab =>
    if hz : a.isZero = true then i.runSharedWithTerminalIndexed terminalProgram N bits
        (.ready (choice.select false)) (i.choice_select_invariant choice hCursor false) pos hpos else
      if he : a.same b = true then i.runSharedWithTerminalIndexed terminalProgram N bits
        (.ready (choice.select true)) (i.choice_select_invariant choice hCursor true) pos hpos else
        if hRead : pos < N then
          let next := a.coinStep b
          have hlt : a.value < b.value := lt_of_le_of_ne hab (fun h => he ((a.same_value b).mpr h))
          if bits ⟨pos, hRead⟩ = next.1 then
            i.runSharedWithTerminalIndexed terminalProgram N bits
              (.coin choice next.2 b hb (a.coinStep_normalized b hlt).le) hCursor (pos + 1) (by omega)
          else i.runSharedWithTerminalIndexed terminalProgram N bits
            (.ready (choice.select (!bits ⟨pos, hRead⟩)))
            (i.choice_select_invariant choice hCursor (!bits ⟨pos, hRead⟩)) (pos + 1) (by omega)
        else (none, pos)
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

theorem runSharedWithTerminalIndexed_eq {n : ℕ} (i : RationalLottoResourceSystem n)
    (terminalProgram : i.PhaseResult → RationalAllocationProgram n 80) (K : ℕ) (outerBits scalarBits : Fin K → Bool)
    (hProgram : ∀ value, terminalProgram value = (i.terminalData value).program K outerBits scalarBits)
    (N : ℕ) (bits : Fin N → Bool) (cursor : SharedResourceCursor i.length) (hCursor : i.SharedInvariant cursor)
    (pos : ℕ) (hpos : pos ≤ N) :
    i.runSharedWithTerminalIndexed terminalProgram N bits cursor hCursor pos hpos =
      i.runSharedIndexed K outerBits scalarBits N bits cursor hCursor pos hpos := by
  revert hCursor
  cases hCursorEq : cursor with
  | ready state =>
    intro hCursor
    conv_lhs => unfold runSharedWithTerminalIndexed
    conv_rhs => unfold runSharedIndexed
    split
    · rename_i value hp
      split
      · rename_i other hOther
        have hEq : value = other := ResourcePreparation.done.inj (hp.symm.trans hOther)
        subst other
        exact congrArg (fun program : RationalAllocationProgram n 80 =>
          program.machine.runCachedIndexed N bits (.state program.start) pos hpos)
          (hProgram ⟨value, i.shared_done_terminal state hCursor value hp⟩)
      · rename_i p hOther
        cases hp.symm.trans hOther
    · rename_i p hp
      split
      · rename_i value hOther
        cases hp.symm.trans hOther
      · rename_i other hOther
        have hEq : p = other := ResourcePreparation.ask.inj (hp.symm.trans hOther)
        subst other
        exact i.runSharedWithTerminalIndexed_eq terminalProgram K outerBits scalarBits hProgram N bits
          (SharedResourceCursor.prepared p) (i.shared_prepared_invariant state hCursor p hp) pos hpos
  | coin choice a b hb hab =>
    intro hCursor
    conv_lhs => unfold runSharedWithTerminalIndexed
    conv_rhs => unfold runSharedIndexed
    by_cases hz : a.isZero = true
    · simp only [dite_eq_left hz]
      exact i.runSharedWithTerminalIndexed_eq terminalProgram K outerBits scalarBits hProgram N bits
        (.ready (choice.select false)) (i.choice_select_invariant choice hCursor false) pos hpos
    · simp only [dite_eq_right hz]
      by_cases he : a.same b = true
      · simp only [dite_eq_left he]
        exact i.runSharedWithTerminalIndexed_eq terminalProgram K outerBits scalarBits hProgram N bits
          (.ready (choice.select true)) (i.choice_select_invariant choice hCursor true) pos hpos
      · simp only [dite_eq_right he]
        by_cases hRead : pos < N
        · simp only [dite_eq_left hRead]
          by_cases hd : bits ⟨pos, hRead⟩ = (a.coinStep b).1
          · simp only [ite_eq_left hd]
            have hlt : a.value < b.value := lt_of_le_of_ne hab (fun h => he ((a.same_value b).mpr h))
            exact i.runSharedWithTerminalIndexed_eq terminalProgram K outerBits scalarBits hProgram N bits
              (.coin choice (a.coinStep b).2 b hb (a.coinStep_normalized b hlt).le) hCursor (pos + 1) (by omega)
          · simp only [ite_eq_right hd]
            exact i.runSharedWithTerminalIndexed_eq terminalProgram K outerBits scalarBits hProgram N bits
              (.ready (choice.select (!bits ⟨pos, hRead⟩)))
              (i.choice_select_invariant choice hCursor (!bits ⟨pos, hRead⟩)) (pos + 1) (by omega)
        · simp only [dite_eq_right hRead]
termination_by (N - pos, cursor.rank)
decreasing_by
  all_goals simp only [hCursorEq]
  all_goals first
    | (apply Prod.Lex.right; apply SharedResourceCursor.prepared_rank_lt; assumption)
    | (apply Prod.Lex.right; exact SharedResourceCursor.selected_rank_lt choice a b hb hab false)
    | (apply Prod.Lex.right; exact SharedResourceCursor.selected_rank_lt choice a b hb hab true)
    | (apply Prod.Lex.left; omega)

end Blotto.RationalLottoResourceSystem
