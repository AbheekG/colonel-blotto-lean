import Blotto.SharedResourceCallbackWork

/-! Event-work refinement is independent of output refinement. It preserves
arbitrary source-callback prices, including the final selected update before
source completion and the absence of update charges at exhaustion. -/

namespace Blotto.SharedResourceCursor

theorem selected_callbackWork {n : ℕ} {L : Fin n → ℚ} (charge : RationalResourceCursor L → ℕ)
    (N : ℕ) (bits : Fin N → Bool) (choice : ResourceChoice L) (branch : Bool) (pos : ℕ) (hpos : pos ≤ N) :
    charge (choice.successor branch) +
      (rationalResourceMachine L).cachedCallbackTailWork charge N bits (.ready (choice.select branch)) pos hpos =
      (rationalResourceMachine L).cachedCallbackWork charge N bits (.state (choice.successor branch)) pos hpos := by
  rw [WordStateMachine.cachedCallbackWork_state]
  rfl

theorem callbackWork_refines {n : ℕ} {L : Fin n → ℚ} (charge : RationalResourceCursor L → ℕ)
    (N : ℕ) (bits : Fin N → Bool) (cursor : SharedResourceCursor L) (incoming : ℕ) (pos : ℕ) (hpos : pos ≤ N) :
    callbackWork charge N bits cursor incoming pos hpos = callbackWorkReference charge N bits cursor incoming pos hpos := by
  cases cursor with
  | ready state =>
    conv_lhs => unfold callbackWork
    conv_rhs =>
      unfold callbackWorkReference
      dsimp only
      unfold WordStateMachine.cachedCallbackTailWork
    cases hp : prepareResourceChoice state with
    | done value =>
      have he := prepareResourceChoice_refines state
      rw [hp] at he
      change WordTransition.done value = (rationalResourceMachine L).step (.ready state) at he
      rw [← he]
    | ask p =>
      rw [prepare_step state p hp]
      have ih := callbackWork_refines charge N bits (prepared p) 0 pos hpos
      simpa only [callbackWorkReference, decode_prepared, CachedWordCursor.ofWords, prepared]
        using congrArg (fun w => incoming + w) ih
  | coin choice a b hb hab =>
    conv_lhs => unfold callbackWork
    conv_rhs =>
      unfold callbackWorkReference
      dsimp only
      unfold WordStateMachine.cachedCallbackWork
    by_cases hz : a.isZero = true
    · simp only [dite_eq_left hz]
      have ih := callbackWork_refines charge N bits (.ready (choice.select false)) (charge (choice.successor false)) pos hpos
      rw [callbackWorkReference] at ih
      exact ih.trans (selected_callbackWork charge N bits choice false pos hpos)
    simp only [dite_eq_right hz]
    by_cases he : a.same b = true
    · simp only [dite_eq_left he]
      have ih := callbackWork_refines charge N bits (.ready (choice.select true)) (charge (choice.successor true)) pos hpos
      rw [callbackWorkReference] at ih
      exact ih.trans (selected_callbackWork charge N bits choice true pos hpos)
    simp only [dite_eq_right he]
    by_cases hRead : pos < N
    · simp only [dite_eq_left hRead]
      have hlt : a.value < b.value := lt_of_le_of_ne hab (fun h => he ((a.same_value b).mpr h))
      by_cases hd : bits ⟨pos, hRead⟩ = (a.coinStep b).1
      · simp only [ite_eq_left hd]
        exact callbackWork_refines charge N bits (.coin choice (a.coinStep b).2 b hb (a.coinStep_normalized b hlt).le) 0 (pos + 1) (by omega)
      · simp only [ite_eq_right hd]
        have ih := callbackWork_refines charge N bits (.ready (choice.select (!bits ⟨pos, hRead⟩)))
          (charge (choice.successor (!bits ⟨pos, hRead⟩))) (pos + 1) (by omega)
        cases hBit : bits ⟨pos, hRead⟩
        · simp only [hBit, Bool.not_false, Bool.false_eq_true, ite_false] at ih ⊢
          rw [callbackWorkReference] at ih
          exact ih.trans (selected_callbackWork charge N bits choice true (pos + 1) (by omega))
        · simp only [hBit, Bool.not_true, ite_true] at ih ⊢
          rw [callbackWorkReference] at ih
          exact ih.trans (selected_callbackWork charge N bits choice false (pos + 1) (by omega))
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

def runCallbackWork {n : ℕ} {L : Fin n → ℚ} (charge : RationalResourceCursor L → ℕ)
    (R : ℕ) (state : RationalActiveResources L) (bits : Fin R → Bool) : ℕ :=
  callbackWork charge R bits (.ready state) (charge (.ready state)) 0 (Nat.zero_le R)

theorem runCallbackWork_refines {n : ℕ} {L : Fin n → ℚ} (charge : RationalResourceCursor L → ℕ)
    (R : ℕ) (state : RationalActiveResources L) (bits : Fin R → Bool) :
    runCallbackWork charge R state bits = (rationalResourceMachine L).runCachedCallbackWork charge R (.ready state) bits := by
  rw [runCallbackWork, callbackWork_refines, callbackWorkReference]
  exact ((rationalResourceMachine L).cachedCallbackWork_state charge R bits (.ready state) 0 (Nat.zero_le R)).symm

end Blotto.SharedResourceCursor
