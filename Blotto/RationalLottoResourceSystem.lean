import Blotto.RationalTerminalGroupInputs
import Blotto.WordMachineRestriction
import Blotto.RationalResourceMean

/-! Native rational input, invariant-carrying resource phase and terminal
compiler for arbitrary field count. All mathematical certificates erase. -/

namespace Blotto
open scoped BigOperators

structure RationalLottoResourceSystem (n : ℕ) where
  B : ℚ
  length : Fin n → ℚ
  initial : Fin n → ℚ
  B_pos : 0 < B
  length_pos : ∀ j, 0 < length j
  length_le : ∀ j, length j ≤ B
  initial_box : ∀ j, 0 ≤ initial j ∧ initial j ≤ length j
  initial_sum : (∑ j, initial j) = 2 * B

namespace RationalLottoResourceSystem

noncomputable def real {n : ℕ} (i : RationalLottoResourceSystem n) : LottoResourceSystem n where
  B := i.B
  length := fun j => i.length j
  initial := fun j => i.initial j
  B_pos := by exact_mod_cast i.B_pos
  length_pos := fun j => by exact_mod_cast i.length_pos j
  length_le := fun j => by exact_mod_cast i.length_le j
  initial_box := fun j => by
    change (0 : ℝ) ≤ (i.initial j : ℝ) ∧ (i.initial j : ℝ) ≤ (i.length j : ℝ)
    exact_mod_cast i.initial_box j
  initial_sum := by exact_mod_cast i.initial_sum

def initialState {n : ℕ} (i : RationalLottoResourceSystem n) : RationalActiveResources i.length :=
  RationalActiveResources.initial i.length i.initial

theorem initial_invariant {n : ℕ} (i : RationalLottoResourceSystem n) :
    RationalResourceInvariant i.length (2 * (i.B : ℝ)) i.initialState := by
  constructor
  · intro j
    change (0 : ℝ) ≤ ((RationalResourceArray.ofAllocation i.initial).allocation j : ℝ) ∧
      ((RationalResourceArray.ofAllocation i.initial).allocation j : ℝ) ≤ (i.length j : ℝ)
    rw [RationalResourceArray.allocation_ofAllocation]
    exact_mod_cast i.initial_box j
  · change (∑ j, ((RationalResourceArray.ofAllocation i.initial).allocation j : ℝ)) = 2 * (i.B : ℝ)
    rw [RationalResourceArray.allocation_ofAllocation]
    exact_mod_cast i.initial_sum

def CursorInvariant {n : ℕ} (i : RationalLottoResourceSystem n) (cursor : RationalResourceCursor i.length) : Prop :=
  RationalResourceInvariant i.length (2 * (i.B : ℝ)) cursor.materialize

def TerminalState {n : ℕ} (i : RationalLottoResourceSystem n) (s : RationalActiveResources i.length) : Prop :=
  RationalResourceInvariant i.length (2 * (i.B : ℝ)) s ∧ s.active.length ≤ 1

theorem phaseProof {n : ℕ} (i : RationalLottoResourceSystem n) :
    ∀ cursor : RationalResourceCursor i.length, i.CursorInvariant cursor →
      ((rationalResourceMachine i.length).step cursor).Postcondition i.CursorInvariant i.TerminalState := by
  intro cursor hs
  have hi := rationalResourceStep_invariant (2 * (i.B : ℝ)) cursor.materialize hs
  have ht := rationalResourceStep_terminal cursor.materialize
  unfold rationalResourceMachine rationalResourceTransition
  dsimp only
  cases he : rationalResourceStep cursor.materialize with
  | done value => rw [he] at hi ht; exact ⟨hi, ht⟩
  | ask a b hb hab upper lower => rw [he] at hi; exact hi

abbrev PhaseCursor {n : ℕ} (i : RationalLottoResourceSystem n) :=
  {cursor : RationalResourceCursor i.length // i.CursorInvariant cursor}
abbrev PhaseResult {n : ℕ} (i : RationalLottoResourceSystem n) :=
  {s : RationalActiveResources i.length // i.TerminalState s}

def phase {n : ℕ} (i : RationalLottoResourceSystem n) : WordStateMachine i.PhaseCursor i.PhaseResult :=
  (rationalResourceMachine i.length).restricted i.CursorInvariant i.TerminalState i.phaseProof

def start {n : ℕ} (i : RationalLottoResourceSystem n) : i.PhaseCursor := ⟨.ready i.initialState, i.initial_invariant⟩

def terminalData {n : ℕ} (i : RationalLottoResourceSystem n) (s : i.PhaseResult) : RationalTerminalLotto n :=
  RationalTerminalLotto.ofActive i.B i.length i.B_pos i.length_pos i.length_le s.1 s.2.1 s.2.2

theorem phase_rank {n : ℕ} (i : RationalLottoResourceSystem n) : i.phase.rank i.start ≤ n - 1 :=
  rationalResourceMachine_initial_rank _ _

theorem phase_mean {n : ℕ} (i : RationalLottoResourceSystem n) (j : Fin n) :
    (i.phase.specification i.start).decode.mean (fun s => ((i.terminalData s).resource j : ℝ)) = (i.initial j : ℝ) := by
  change (((rationalResourceMachine i.length).restricted i.CursorInvariant i.TerminalState i.phaseProof).specification
    i.start).decode.mean (fun s => s.1.resource.realAllocation j) = (i.initial j : ℝ)
  rw [WordStateMachine.restricted_mean (rationalResourceMachine i.length) i.CursorInvariant i.TerminalState i.phaseProof
    i.start (fun s : RationalActiveResources i.length => s.resource.realAllocation j)]
  rw [rationalResourceMachine_mean]
  change ((RationalResourceArray.ofAllocation i.initial).allocation j : ℝ) = (i.initial j : ℝ)
  rw [RationalResourceArray.allocation_ofAllocation]

end RationalLottoResourceSystem
end Blotto
