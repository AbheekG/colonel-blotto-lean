import Blotto.SharedResourceCursor
import Blotto.RationalLottoProgram

/-! Erased hard-budget invariants for one-state pending resource control.
The retained state belongs to one source phase; each selected endpoint keeps
the original box and sum, and completion supplies the terminal input proof. -/

namespace Blotto.ResourcePreparation

def owner {n : ℕ} {L : Fin n → ℚ} : ResourcePreparation L → RationalActiveResources L
  | .done state => state
  | .ask p => p.choice.state

end Blotto.ResourcePreparation
namespace Blotto

theorem prepareResourceChoice_owner {n : ℕ} {L : Fin n → ℚ} (state : RationalActiveResources L) :
    (prepareResourceChoice state).owner = state := by
  cases state with
  | mk resource active hn hm =>
    cases active with
    | nil => rfl
    | cons a rest => cases rest <;> rfl

end Blotto
namespace Blotto.RationalLottoResourceSystem

def SharedInvariant {n : ℕ} (i : RationalLottoResourceSystem n) : SharedResourceCursor i.length → Prop
  | .ready state => RationalResourceInvariant i.length (2 * (i.B : ℝ)) state
  | .coin choice _ _ _ _ => RationalResourceInvariant i.length (2 * (i.B : ℝ)) choice.state

theorem choice_select_invariant {n : ℕ} (i : RationalLottoResourceSystem n) (choice : ResourceChoice i.length)
    (hState : RationalResourceInvariant i.length (2 * (i.B : ℝ)) choice.state) (branch : Bool) :
    RationalResourceInvariant i.length (2 * (i.B : ℝ)) (choice.select branch) := by
  have hEndpoint : (if branch then choice.upper else choice.lower) =
      (choice.state.pair choice.first choice.second choice.tail choice.head_pair).lower ∨
      (if branch then choice.upper else choice.lower) =
      (choice.state.pair choice.first choice.second choice.tail choice.head_pair).upper := by
    cases branch
    · exact Or.inl choice.lower_correct
    · exact Or.inr choice.upper_correct
  exact ⟨choice.state.update_inBox choice.first choice.second choice.tail choice.head_pair hState.1 hEndpoint,
    (choice.state.update_sum choice.first choice.second choice.tail choice.head_pair _).trans hState.2⟩

theorem shared_prepared_invariant {n : ℕ} (i : RationalLottoResourceSystem n) (state : RationalActiveResources i.length)
    (hState : RationalResourceInvariant i.length (2 * (i.B : ℝ)) state) (p : PreparedResourceChoice i.length)
    (hPrepare : prepareResourceChoice state = .ask p) : i.SharedInvariant (SharedResourceCursor.prepared p) := by
  have hOwner := prepareResourceChoice_owner state
  rw [hPrepare] at hOwner
  change RationalResourceInvariant i.length (2 * (i.B : ℝ)) p.choice.state
  change p.choice.state = state at hOwner
  rw [hOwner]
  exact hState

theorem shared_done_terminal {n : ℕ} (i : RationalLottoResourceSystem n) (state : RationalActiveResources i.length)
    (hState : RationalResourceInvariant i.length (2 * (i.B : ℝ)) state) (value : RationalActiveResources i.length)
    (hPrepare : prepareResourceChoice state = .done value) : i.TerminalState value := by
  have hStep := prepareResourceChoice_refines state
  rw [hPrepare] at hStep
  change WordTransition.done value = (rationalResourceMachine i.length).step (.ready state) at hStep
  have hp := i.phaseProof (.ready state) hState
  rw [← hStep] at hp
  exact hp

def decodeSharedSource {n : ℕ} (i : RationalLottoResourceSystem n) (K : ℕ) (outerBits scalarBits : Fin K → Bool)
    (cursor : SharedResourceCursor i.length) (hCursor : i.SharedInvariant cursor) :
    CachedWordCursor (SerialState i.PhaseCursor i.PhaseResult (fun value => ((i.terminalData value).program K outerBits scalarBits).State)) :=
  match cursor with
  | .ready state => .state (.source ⟨.ready state, hCursor⟩)
  | .coin choice a b hb hab => .coin a b hb hab
      (.source ⟨choice.successor true, i.choice_select_invariant choice hCursor true⟩)
      (.source ⟨choice.successor false, i.choice_select_invariant choice hCursor false⟩)

end Blotto.RationalLottoResourceSystem
