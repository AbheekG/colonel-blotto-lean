import Blotto.SharedResourceBudget
import Blotto.SharedResourceRun
import Blotto.RationalLottoProgram

/-! One-state resource control hands its unchanged bit reader/position to the
existing terminal coupling. Erased invariants supply the terminal input proof;
there is one shared cap and no intermediate allocation-law/tree expansion. -/

namespace Blotto.RationalLottoResourceSystem

def runSharedIndexed {n : ℕ} (i : RationalLottoResourceSystem n) (K : ℕ) (outerBits scalarBits : Fin K → Bool)
    (N : ℕ) (bits : Fin N → Bool) (cursor : SharedResourceCursor i.length) (hCursor : i.SharedInvariant cursor)
    (pos : ℕ) (hpos : pos ≤ N) : Option (Fin n → ℚ) × ℕ :=
  match cursor with
  | .ready state => match hp : prepareResourceChoice state with
    | .done value =>
      let terminal : i.PhaseResult := ⟨value, i.shared_done_terminal state hCursor value hp⟩
      let program := (i.terminalData terminal).program K outerBits scalarBits
      program.machine.runCachedIndexed N bits (.state program.start) pos hpos
    | .ask p => i.runSharedIndexed K outerBits scalarBits N bits (SharedResourceCursor.prepared p)
        (i.shared_prepared_invariant state hCursor p hp) pos hpos
  | .coin choice a b hb hab =>
    if hz : a.isZero = true then i.runSharedIndexed K outerBits scalarBits N bits
        (.ready (choice.select false)) (i.choice_select_invariant choice hCursor false) pos hpos else
      if he : a.same b = true then i.runSharedIndexed K outerBits scalarBits N bits
        (.ready (choice.select true)) (i.choice_select_invariant choice hCursor true) pos hpos else
        if hRead : pos < N then
          let next := a.coinStep b
          have hlt : a.value < b.value := lt_of_le_of_ne hab (fun h => he ((a.same_value b).mpr h))
          if bits ⟨pos, hRead⟩ = next.1 then
            i.runSharedIndexed K outerBits scalarBits N bits
              (.coin choice next.2 b hb (a.coinStep_normalized b hlt).le) hCursor (pos + 1) (by omega)
          else i.runSharedIndexed K outerBits scalarBits N bits
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

def runShared {n : ℕ} (i : RationalLottoResourceSystem n) (K R : ℕ)
    (outerBits scalarBits : Fin K → Bool) (choiceBits : Fin R → Bool) : Option (Fin n → ℚ) × ℕ :=
  i.runSharedIndexed K outerBits scalarBits R choiceBits (.ready i.initialState) i.initial_invariant 0 (Nat.zero_le R)

end Blotto.RationalLottoResourceSystem
