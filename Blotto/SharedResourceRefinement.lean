import Blotto.SharedResourceRun
import Blotto.CachedWordControllerRefinement

/-! The one-state resource interpreter returns exactly the old cached result
and bit position. Decoding constructs the reference successors only in proofs. -/

namespace Blotto.RationalResourceCursor

theorem cachedRun_materialize {n : ℕ} {L : Fin n → ℚ} (N : ℕ) (bits : Fin N → Bool)
    (cursor : RationalResourceCursor L) (pos : ℕ) (hpos : pos ≤ N) :
    (rationalResourceMachine L).runCachedIndexed N bits (.state cursor) pos hpos =
      (rationalResourceMachine L).runCachedIndexed N bits (.state (.ready cursor.materialize)) pos hpos := by
  conv_lhs => unfold WordStateMachine.runCachedIndexed
  conv_rhs => unfold WordStateMachine.runCachedIndexed
  rfl

end Blotto.RationalResourceCursor
namespace Blotto.SharedResourceCursor

theorem runIndexed_refines {n : ℕ} {L : Fin n → ℚ} (N : ℕ) (bits : Fin N → Bool)
    (cursor : SharedResourceCursor L) (pos : ℕ) (hpos : pos ≤ N) :
    runIndexed N bits cursor pos hpos = (rationalResourceMachine L).runCachedIndexed N bits cursor.decode pos hpos := by
  cases hCursorEq : cursor with
  | ready state =>
    conv_lhs => unfold runIndexed
    conv_rhs => rw [decode]; unfold WordStateMachine.runCachedIndexed
    cases hp : prepareResourceChoice state with
    | done value =>
      have he := prepareResourceChoice_refines state
      rw [hp] at he
      change .done value = (rationalResourceMachine L).step (.ready state) at he
      rw [← he]
    | ask p =>
      rw [prepare_step state p hp]
      have ih := runIndexed_refines N bits (prepared p) pos hpos
      simpa only [decode_prepared] using ih
  | coin choice a b hb hab =>
    conv_lhs => unfold runIndexed
    conv_rhs => rw [decode]; unfold WordStateMachine.runCachedIndexed
    by_cases hz : a.isZero = true
    · simp only [dite_eq_left hz]
      have ih := runIndexed_refines N bits (.ready (choice.select false)) pos hpos
      exact ih.trans (RationalResourceCursor.cachedRun_materialize N bits (choice.successor false) pos hpos).symm
    simp only [dite_eq_right hz]
    by_cases he : a.same b = true
    · simp only [dite_eq_left he]
      have ih := runIndexed_refines N bits (.ready (choice.select true)) pos hpos
      exact ih.trans (RationalResourceCursor.cachedRun_materialize N bits (choice.successor true) pos hpos).symm
    simp only [dite_eq_right he]
    by_cases hRead : pos < N
    · simp only [dite_eq_left hRead]
      have hlt : a.value < b.value := lt_of_le_of_ne hab (fun h => he ((a.same_value b).mpr h))
      by_cases hd : bits ⟨pos, hRead⟩ = (a.coinStep b).1
      · simp only [ite_eq_left hd]
        exact runIndexed_refines N bits (.coin choice (a.coinStep b).2 b hb (a.coinStep_normalized b hlt).le)
          (pos + 1) (by omega)
      · simp only [ite_eq_right hd]
        have ih := runIndexed_refines N bits (.ready (choice.select (!bits ⟨pos, hRead⟩))) (pos + 1) (by omega)
        cases hBit : bits ⟨pos, hRead⟩
        · simp only [hBit, Bool.not_false, Bool.false_eq_true, ite_false] at ih ⊢
          exact ih.trans (RationalResourceCursor.cachedRun_materialize N bits (choice.successor true) (pos + 1) (by omega)).symm
        · simp only [hBit, Bool.not_true, ite_true] at ih ⊢
          exact ih.trans (RationalResourceCursor.cachedRun_materialize N bits (choice.successor false) (pos + 1) (by omega)).symm
    · simp only [dite_eq_right hRead]
termination_by (N - pos, cursor.rank)
decreasing_by
  · apply Prod.Lex.right
    exact prepared_rank_lt state p hp
  · apply Prod.Lex.right
    exact selected_rank_lt choice a b hb hab false
  · apply Prod.Lex.right
    exact selected_rank_lt choice a b hb hab true
  all_goals apply Prod.Lex.left
  all_goals omega

theorem run_refines {n : ℕ} {L : Fin n → ℚ} (N : ℕ) (state : RationalActiveResources L) (bits : Fin N → Bool) :
    run N state bits = (rationalResourceMachine L).run N (.ready state) bits :=
  runIndexed_refines N bits (.ready state) 0 (Nat.zero_le N)

end Blotto.SharedResourceCursor
