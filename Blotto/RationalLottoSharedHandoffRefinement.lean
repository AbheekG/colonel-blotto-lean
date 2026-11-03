import Blotto.RationalLottoSharedHandoffBridge

/-! Universal primary handoff-work refinement preserves one-time preparation
and arbitrary terminal callback prices at the existing cap and position. -/

namespace Blotto.RationalLottoResourceSystem

theorem sharedHandoffWork_refines {n : ℕ} (i : RationalLottoResourceSystem n) (K : ℕ)
    (outerBits scalarBits : Fin K → Bool) (cost : i.PhaseResult → ℕ)
    (terminalCharge : ∀ value : i.PhaseResult, ((i.terminalData value).program K outerBits scalarBits).State → ℕ) (N : ℕ) (bits : Fin N → Bool)
    (cursor : SharedResourceCursor i.length) (hCursor : i.SharedInvariant cursor) (pos : ℕ) (hpos : pos ≤ N) :
    i.sharedHandoffWork K outerBits scalarBits cost terminalCharge N bits cursor hCursor pos hpos =
      (i.machine K outerBits scalarBits).cachedCallbackWork (i.handoffCharge K outerBits scalarBits cost terminalCharge) N bits
        (i.decodeSharedSource K outerBits scalarBits cursor hCursor) pos hpos := by
  revert hCursor
  cases hCursorEq : cursor with
  | ready state =>
    intro hCursor
    conv_lhs => rw [sharedHandoffWork.eq_1]
    split
    · rename_i value hp
      exact (i.shared_source_done_handoffWork K outerBits scalarBits cost terminalCharge state hCursor value hp N bits pos hpos).symm
    · rename_i p hp
      conv_rhs =>
        rw [decodeSharedSource.eq_def]
        dsimp only
        unfold WordStateMachine.cachedCallbackWork
      have hStep : (i.machine K outerBits scalarBits).step (.source ⟨.ready state, hCursor⟩) =
          .ask p.words.numerator p.words.denominator p.words.denominator_pos p.words.normalized
            (.source ⟨p.choice.successor true, i.choice_select_invariant p.choice (i.shared_prepared_invariant state hCursor p hp) true⟩)
            (.source ⟨p.choice.successor false, i.choice_select_invariant p.choice (i.shared_prepared_invariant state hCursor p hp) false⟩) := by
        simp only [machine, WordStateMachine.serial, serialTransition, i.shared_prepare_phase_ask state hCursor p hp]
      rw [hStep, i.shared_source_ask_handoffCharge K outerBits scalarBits cost terminalCharge state hCursor p hp, Nat.zero_add]
      exact i.sharedHandoffWork_refines K outerBits scalarBits cost terminalCharge N bits (SharedResourceCursor.prepared p)
        (i.shared_prepared_invariant state hCursor p hp) pos hpos
  | coin choice a b hb hab =>
    intro hCursor
    conv_lhs => unfold sharedHandoffWork
    conv_rhs =>
      rw [decodeSharedSource.eq_def]
      dsimp only
      unfold WordStateMachine.cachedCallbackWork
    by_cases hz : a.isZero = true
    · simp only [dite_eq_left hz]
      have ih := i.sharedHandoffWork_refines K outerBits scalarBits cost terminalCharge N bits (.ready (choice.select false))
        (i.choice_select_invariant choice hCursor false) pos hpos
      exact ih.trans (i.materialized_source_handoffWork K outerBits scalarBits cost terminalCharge
        ⟨choice.successor false, i.choice_select_invariant choice hCursor false⟩ N bits pos hpos).symm
    simp only [dite_eq_right hz]
    by_cases he : a.same b = true
    · simp only [dite_eq_left he]
      have ih := i.sharedHandoffWork_refines K outerBits scalarBits cost terminalCharge N bits (.ready (choice.select true))
        (i.choice_select_invariant choice hCursor true) pos hpos
      exact ih.trans (i.materialized_source_handoffWork K outerBits scalarBits cost terminalCharge
        ⟨choice.successor true, i.choice_select_invariant choice hCursor true⟩ N bits pos hpos).symm
    simp only [dite_eq_right he]
    by_cases hRead : pos < N
    · simp only [dite_eq_left hRead]
      have hlt : a.value < b.value := lt_of_le_of_ne hab (fun h => he ((a.same_value b).mpr h))
      by_cases hd : bits ⟨pos, hRead⟩ = (a.coinStep b).1
      · simp only [ite_eq_left hd]
        exact i.sharedHandoffWork_refines K outerBits scalarBits cost terminalCharge N bits
          (.coin choice (a.coinStep b).2 b hb (a.coinStep_normalized b hlt).le) hCursor (pos + 1) (by omega)
      · simp only [ite_eq_right hd]
        have ih := i.sharedHandoffWork_refines K outerBits scalarBits cost terminalCharge N bits
          (.ready (choice.select (!bits ⟨pos, hRead⟩)))
          (i.choice_select_invariant choice hCursor (!bits ⟨pos, hRead⟩)) (pos + 1) (by omega)
        by_cases hBit : bits ⟨pos, hRead⟩ = true
        · simp only [hBit, Bool.not_true, ite_true] at ih ⊢
          exact ih.trans (i.materialized_source_handoffWork K outerBits scalarBits cost terminalCharge
            ⟨choice.successor false, i.choice_select_invariant choice hCursor false⟩ N bits (pos + 1) (by omega)).symm
        · have hFalse : bits ⟨pos, hRead⟩ = false := by
            cases hValue : bits ⟨pos, hRead⟩ <;> simp_all
          simp only [hFalse, Bool.not_false, Bool.false_eq_true, ite_false] at ih ⊢
          exact ih.trans (i.materialized_source_handoffWork K outerBits scalarBits cost terminalCharge
            ⟨choice.successor true, i.choice_select_invariant choice hCursor true⟩ N bits (pos + 1) (by omega)).symm
    · simp only [dite_eq_right hRead]
termination_by (N - pos, cursor.rank)
decreasing_by
  all_goals simp only [hCursorEq]
  · apply Prod.Lex.right
    apply SharedResourceCursor.prepared_rank_lt
    assumption
  · apply Prod.Lex.right
    exact SharedResourceCursor.selected_rank_lt choice a b hb hab false
  · apply Prod.Lex.right
    exact SharedResourceCursor.selected_rank_lt choice a b hb hab true
  all_goals apply Prod.Lex.left
  all_goals omega

end Blotto.RationalLottoResourceSystem
