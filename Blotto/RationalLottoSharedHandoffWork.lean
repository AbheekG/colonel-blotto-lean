import Blotto.CachedSerialHandoffWork
import Blotto.RationalLottoSharedBridge

/-! The primary one-state prefix charges terminal preparation at handoff and
then follows arbitrary terminal callback prices at the same cap and position.
Source exhaustion performs neither preparation nor any terminal callback. -/

namespace Blotto.RationalLottoResourceSystem

def handoffCharge {n : ℕ} (i : RationalLottoResourceSystem n) (K : ℕ) (outerBits scalarBits : Fin K → Bool)
    (cost : i.PhaseResult → ℕ)
    (terminalCharge : ∀ value : i.PhaseResult, ((i.terminalData value).program K outerBits scalarBits).State → ℕ) :
    i.SamplingState K outerBits scalarBits → ℕ :=
  WordStateMachine.serialHandoffCharge i.phase
    (fun value => ((i.terminalData value).program K outerBits scalarBits).start) cost terminalCharge

def sharedHandoffWork {n : ℕ} (i : RationalLottoResourceSystem n) (K : ℕ) (outerBits scalarBits : Fin K → Bool)
    (cost : i.PhaseResult → ℕ)
    (terminalCharge : ∀ value : i.PhaseResult, ((i.terminalData value).program K outerBits scalarBits).State → ℕ)
    (N : ℕ) (bits : Fin N → Bool) (cursor : SharedResourceCursor i.length) (hCursor : i.SharedInvariant cursor)
    (pos : ℕ) (hpos : pos ≤ N) : ℕ :=
  match cursor with
  | .ready state => match hp : prepareResourceChoice state with
    | .done value =>
      let terminal : i.PhaseResult := ⟨value, i.shared_done_terminal state hCursor value hp⟩
      let program := (i.terminalData terminal).program K outerBits scalarBits
      cost terminal + program.machine.cachedCallbackWork (terminalCharge terminal) N bits (.state program.start) pos hpos
    | .ask p => i.sharedHandoffWork K outerBits scalarBits cost terminalCharge N bits (SharedResourceCursor.prepared p)
        (i.shared_prepared_invariant state hCursor p hp) pos hpos
  | .coin choice a b hb hab =>
    if hz : a.isZero = true then i.sharedHandoffWork K outerBits scalarBits cost terminalCharge N bits
        (.ready (choice.select false)) (i.choice_select_invariant choice hCursor false) pos hpos else
      if he : a.same b = true then i.sharedHandoffWork K outerBits scalarBits cost terminalCharge N bits
        (.ready (choice.select true)) (i.choice_select_invariant choice hCursor true) pos hpos else
        if hRead : pos < N then
          let next := a.coinStep b
          have hlt : a.value < b.value := lt_of_le_of_ne hab (fun h => he ((a.same_value b).mpr h))
          if bits ⟨pos, hRead⟩ = next.1 then
            i.sharedHandoffWork K outerBits scalarBits cost terminalCharge N bits
              (.coin choice next.2 b hb (a.coinStep_normalized b hlt).le) hCursor (pos + 1) (by omega)
          else i.sharedHandoffWork K outerBits scalarBits cost terminalCharge N bits
            (.ready (choice.select (!bits ⟨pos, hRead⟩)))
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

end Blotto.RationalLottoResourceSystem
