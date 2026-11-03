import Blotto.RationalLottoSharedRun
import Blotto.CachedWordReindex

/-! Runtime bridges for terminal handoff and materialized source states.
They keep the same indexed reader, cap, value and consumed position. -/

namespace Blotto.RationalLottoResourceSystem

theorem continuation_cachedRun {n : ℕ} (i : RationalLottoResourceSystem n) (K : ℕ)
    (outerBits scalarBits : Fin K → Bool) (value : i.PhaseResult)
    (state : ((i.terminalData value).program K outerBits scalarBits).State)
    (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) :
    (i.machine K outerBits scalarBits).runCachedIndexed N bits (.state (.continuation value state)) pos hpos =
      ((i.terminalData value).program K outerBits scalarBits).machine.runCachedIndexed N bits (.state state) pos hpos := by
  have h := ((i.terminalData value).program K outerBits scalarBits).machine.runCachedIndexed_reindex
    (i.machine K outerBits scalarBits)
    (fun s => (SerialState.continuation value s : i.SamplingState K outerBits scalarBits))
    (fun s => rfl) N bits (.state state) pos hpos
  exact h

theorem materialized_source_cachedRun {n : ℕ} (i : RationalLottoResourceSystem n) (K : ℕ)
    (outerBits scalarBits : Fin K → Bool) (cursor : i.PhaseCursor)
    (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) :
    (i.machine K outerBits scalarBits).runCachedIndexed N bits (.state (.source cursor)) pos hpos =
      (i.machine K outerBits scalarBits).runCachedIndexed N bits
        (.state (.source ⟨.ready cursor.1.materialize, cursor.2⟩)) pos hpos := by
  apply WordStateMachine.runCachedIndexed_state_eq
  rfl

theorem shared_prepare_phase_ask {n : ℕ} (i : RationalLottoResourceSystem n)
    (state : RationalActiveResources i.length) (hState : RationalResourceInvariant i.length (2 * (i.B : ℝ)) state)
    (p : PreparedResourceChoice i.length) (hp : prepareResourceChoice state = .ask p) :
    i.phase.step ⟨.ready state, hState⟩ =
      .ask p.words.numerator p.words.denominator p.words.denominator_pos p.words.normalized
        ⟨p.choice.successor true, i.choice_select_invariant p.choice (i.shared_prepared_invariant state hState p hp) true⟩
        ⟨p.choice.successor false, i.choice_select_invariant p.choice (i.shared_prepared_invariant state hState p hp) false⟩ := by
  exact WordTransition.restrict_ask i.CursorInvariant i.TerminalState
    ((rationalResourceMachine i.length).step (.ready state)) (i.phaseProof (.ready state) hState)
    p.words.numerator p.words.denominator p.words.denominator_pos p.words.normalized
    (p.choice.successor true) (p.choice.successor false) (SharedResourceCursor.prepare_step state p hp)

theorem shared_prepare_phase_done {n : ℕ} (i : RationalLottoResourceSystem n)
    (state : RationalActiveResources i.length) (hState : RationalResourceInvariant i.length (2 * (i.B : ℝ)) state)
    (value : RationalActiveResources i.length) (hp : prepareResourceChoice state = .done value) :
    i.phase.step ⟨.ready state, hState⟩ = .done ⟨value, i.shared_done_terminal state hState value hp⟩ := by
  have he := prepareResourceChoice_refines state
  rw [hp] at he
  exact WordTransition.restrict_done i.CursorInvariant i.TerminalState
    ((rationalResourceMachine i.length).step (.ready state)) (i.phaseProof (.ready state) hState) value he.symm

theorem shared_source_done_cachedRun {n : ℕ} (i : RationalLottoResourceSystem n) (K : ℕ)
    (outerBits scalarBits : Fin K → Bool) (state : RationalActiveResources i.length)
    (hState : RationalResourceInvariant i.length (2 * (i.B : ℝ)) state) (value : RationalActiveResources i.length)
    (hp : prepareResourceChoice state = .done value) (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) :
    (i.machine K outerBits scalarBits).runCachedIndexed N bits (.state (.source ⟨.ready state, hState⟩)) pos hpos =
      ((i.terminalData ⟨value, i.shared_done_terminal state hState value hp⟩).program K outerBits scalarBits).machine.runCachedIndexed
        N bits (.state ((i.terminalData ⟨value, i.shared_done_terminal state hState value hp⟩).program K outerBits scalarBits).start) pos hpos := by
  let terminal : i.PhaseResult := ⟨value, i.shared_done_terminal state hState value hp⟩
  have he : (i.machine K outerBits scalarBits).step (.source ⟨.ready state, hState⟩) =
      (i.machine K outerBits scalarBits).step (.continuation terminal ((i.terminalData terminal).program K outerBits scalarBits).start) := by
    simp only [terminal, machine, WordStateMachine.serial, serialTransition, i.shared_prepare_phase_done state hState value hp]
  rw [WordStateMachine.runCachedIndexed_state_eq _ _ _ he]
  exact i.continuation_cachedRun K outerBits scalarBits terminal _ N bits pos hpos

end Blotto.RationalLottoResourceSystem
