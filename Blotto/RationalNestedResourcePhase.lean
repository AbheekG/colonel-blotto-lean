import Blotto.RationalNestedResourceSystem
import Blotto.WordMachineRestriction

/-! The three-resource controller carries its budget/box invariant through
every state and returns certified terminal data. It retains the concrete
native transitions and exact resource-coordinate means, with rank at most two. -/

namespace Blotto.RationalNestedResourceSystem

def CursorInvariant (i : RationalNestedResourceSystem) (cursor : RationalResourceCursor i.capacity) : Prop :=
  RationalResourceInvariant i.capacity (i.totalResource : ℝ) cursor.materialize

def TerminalState (i : RationalNestedResourceSystem) (s : RationalActiveResources i.capacity) : Prop :=
  RationalResourceInvariant i.capacity (i.totalResource : ℝ) s ∧ s.active.length ≤ 1

theorem phase_invariant (i : RationalNestedResourceSystem) (cursor : RationalResourceCursor i.capacity) :
    i.CursorInvariant cursor → ((rationalResourceMachine i.capacity).step cursor).Postcondition i.CursorInvariant i.TerminalState := by
  intro hs
  have hi := rationalResourceStep_invariant (i.totalResource : ℝ) cursor.materialize hs
  have ht := rationalResourceStep_terminal cursor.materialize
  unfold rationalResourceMachine rationalResourceTransition
  dsimp only
  cases he : rationalResourceStep cursor.materialize with
  | done value => rw [he] at hi ht; exact ⟨hi, ht⟩
  | ask a b hb hab upper lower => rw [he] at hi; exact hi

theorem phaseProof (i : RationalNestedResourceSystem) :
    ∀ s : RationalResourceCursor i.capacity, i.CursorInvariant s →
      ((rationalResourceMachine i.capacity).step s).Postcondition i.CursorInvariant i.TerminalState := by
  intro s hs
  convert! i.phase_invariant s hs using 1

def phase (i : RationalNestedResourceSystem) :
    WordStateMachine {cursor : RationalResourceCursor i.capacity // i.CursorInvariant cursor}
      {s : RationalActiveResources i.capacity // i.TerminalState s} :=
  (rationalResourceMachine i.capacity).restricted i.CursorInvariant i.TerminalState i.phaseProof

def start (i : RationalNestedResourceSystem) : {cursor : RationalResourceCursor i.capacity // i.CursorInvariant cursor} :=
  ⟨.ready i.initialState, i.initial_invariant⟩

def terminalData (i : RationalNestedResourceSystem) (s : {s : RationalActiveResources i.capacity // i.TerminalState s}) :
    RationalTerminalResources := i.terminal s.1 s.2.1 s.2.2

theorem phase_rank (i : RationalNestedResourceSystem) : i.phase.rank i.start ≤ 2 := i.initial_rank

theorem phase_mean (i : RationalNestedResourceSystem) (j : Fin 3) :
    (i.phase.specification i.start).decode.mean (fun s => (i.terminalData s).real.resource j) = (i.initial j : ℝ) := by
  change (((rationalResourceMachine i.capacity).restricted i.CursorInvariant i.TerminalState i.phaseProof).specification
    i.start).decode.mean (fun s => s.1.resource.realAllocation j) = (i.initial j : ℝ)
  rw [WordStateMachine.restricted_mean (rationalResourceMachine i.capacity) i.CursorInvariant i.TerminalState i.phaseProof
    i.start (fun s : RationalActiveResources i.capacity => s.resource.realAllocation j)]
  rw [rationalResourceMachine_mean]
  change (i.initialState.resource.allocation j : ℝ) = (i.initial j : ℝ)
  rw [i.initialState_allocation]

end Blotto.RationalNestedResourceSystem
