import Blotto.RationalLottoSharedHandoffWork

/-! Terminal handoff and materialized-source bridges preserve work prices,
not merely output values. A source completion pays preparation once. -/

namespace Blotto.RationalLottoResourceSystem

theorem materialized_source_handoffWork {n : ℕ} (i : RationalLottoResourceSystem n) (K : ℕ)
    (outerBits scalarBits : Fin K → Bool) (cost : i.PhaseResult → ℕ)
    (terminalCharge : ∀ value : i.PhaseResult, ((i.terminalData value).program K outerBits scalarBits).State → ℕ)
    (cursor : i.PhaseCursor) (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) :
    (i.machine K outerBits scalarBits).cachedCallbackWork (i.handoffCharge K outerBits scalarBits cost terminalCharge)
      N bits (.state (.source cursor)) pos hpos =
      (i.machine K outerBits scalarBits).cachedCallbackWork (i.handoffCharge K outerBits scalarBits cost terminalCharge)
        N bits (.state (.source ⟨.ready cursor.1.materialize, cursor.2⟩)) pos hpos := by
  have hStep : (i.machine K outerBits scalarBits).step (.source cursor) =
      (i.machine K outerBits scalarBits).step (.source ⟨.ready cursor.1.materialize, cursor.2⟩) := rfl
  have hTail := (i.machine K outerBits scalarBits).cachedCallbackTailWork_step_eq
    (i.handoffCharge K outerBits scalarBits cost terminalCharge) (.source cursor)
    (.source ⟨.ready cursor.1.materialize, cursor.2⟩) hStep N bits pos hpos
  rw [WordStateMachine.cachedCallbackWork_state, WordStateMachine.cachedCallbackWork_state, hTail]
  rfl

theorem shared_source_done_handoffWork {n : ℕ} (i : RationalLottoResourceSystem n) (K : ℕ)
    (outerBits scalarBits : Fin K → Bool) (cost : i.PhaseResult → ℕ)
    (terminalCharge : ∀ value : i.PhaseResult, ((i.terminalData value).program K outerBits scalarBits).State → ℕ)
    (state : RationalActiveResources i.length) (hState : RationalResourceInvariant i.length (2 * (i.B : ℝ)) state)
    (value : RationalActiveResources i.length) (hp : prepareResourceChoice state = .done value)
    (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) :
    (i.machine K outerBits scalarBits).cachedCallbackWork (i.handoffCharge K outerBits scalarBits cost terminalCharge)
      N bits (.state (.source ⟨.ready state, hState⟩)) pos hpos =
      let terminal : i.PhaseResult := ⟨value, i.shared_done_terminal state hState value hp⟩
      let program := (i.terminalData terminal).program K outerBits scalarBits
      cost terminal + program.machine.cachedCallbackWork (terminalCharge terminal) N bits (.state program.start) pos hpos :=
  i.phase.cachedSerialDoneHandoffWork
    (fun value => ((i.terminalData value).program K outerBits scalarBits).machine)
    (fun value => ((i.terminalData value).program K outerBits scalarBits).start) 80
    (fun value => ((i.terminalData value).program K outerBits scalarBits).rank_le) cost terminalCharge
    ⟨.ready state, hState⟩ ⟨value, i.shared_done_terminal state hState value hp⟩
    (i.shared_prepare_phase_done state hState value hp) N bits pos hpos

theorem shared_source_ask_handoffCharge {n : ℕ} (i : RationalLottoResourceSystem n) (K : ℕ)
    (outerBits scalarBits : Fin K → Bool) (cost : i.PhaseResult → ℕ)
    (terminalCharge : ∀ value : i.PhaseResult, ((i.terminalData value).program K outerBits scalarBits).State → ℕ)
    (state : RationalActiveResources i.length) (hState : RationalResourceInvariant i.length (2 * (i.B : ℝ)) state)
    (p : PreparedResourceChoice i.length) (hp : prepareResourceChoice state = .ask p) :
    i.handoffCharge K outerBits scalarBits cost terminalCharge (.source ⟨.ready state, hState⟩) = 0 := by
  simp only [handoffCharge, WordStateMachine.serialHandoffCharge, i.shared_prepare_phase_ask state hState p hp]

end Blotto.RationalLottoResourceSystem
