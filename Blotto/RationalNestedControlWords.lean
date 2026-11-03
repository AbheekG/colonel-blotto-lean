import Blotto.RationalNestedCallbackInvariant
import Blotto.RationalResourceFieldWords

/-! Source pair words and terminal categorical words share a fixed reached
height bound. The actual words are preserved, including zero/one branches. -/

namespace Blotto.WordTransition

theorem WordsHeight.mono {S α : Type*} {t : WordTransition S α} {s u : ℕ}
    (h : t.WordsHeight s) (hsu : s ≤ u) : t.WordsHeight u := by
  have hp : (2 : ℕ) ^ s ≤ 2 ^ u := by gcongr
  cases t with
  | done value => trivial
  | ask a b hb hab upper lower => exact ⟨h.1.trans_le hp, h.2.trans_le hp⟩

end Blotto.WordTransition
namespace Blotto.RationalNestedResourceSystem

def localControlWordHeight (s : ℕ) : ℕ := (expressionHeightBudget s 54 + 1) * 19

theorem localControlWordHeight_source (s : ℕ) : expressionHeightBudget s 11 ≤ localControlWordHeight s := by
  have hm := expressionHeightBudget_mono s (by decide : 11 ≤ 54)
  unfold localControlWordHeight
  omega

theorem FieldsHeight.phase_wordsHeight {i : RationalNestedResourceSystem} {s : ℕ} (h : i.FieldsHeight s) (hs : 2 ≤ s)
    (cursor : i.PhaseCursor) (hCursor : i.LocalStoreInvariant 2 (expressionHeightBudget s 1) cursor) :
    (i.phase.step cursor).WordsHeight (localControlWordHeight s) := by
  have hp := rationalResourceHeightInvariant_wordsHeight i.capacity 2 _
    (hs.trans (expressionHeightBudget_ge_input s 1)) h.capacity cursor.1 hCursor.1
  rw [expressionHeightBudget_comp] at hp
  exact (WordTransition.restrict_wordsHeight i.CursorInvariant i.TerminalState
    ((rationalResourceMachine i.capacity).step cursor.1) (i.phaseProof cursor.1 cursor.2) _ hp).mono
    (localControlWordHeight_source s)

theorem continuation_wordsHeight (i : RationalNestedResourceSystem) (s K : ℕ) (outerBits scalarBits : Fin K → Bool)
    (value : i.PhaseResult) (state : CategoricalState (Fin 18))
    (hState : state.Bounded 18 (expressionHeightBudget s 54)) :
    ((i.continuationMachine K outerBits scalarBits value).step state).WordsHeight (localControlWordHeight s) :=
  WordTransition.mapValue_wordsHeight
    (fun slot => ((i.terminalData value).profile K outerBits).point K slot scalarBits)
    ((categoricalMachine (0 : Fin 18)).step state) _
    (categoricalTransition_wordsHeight (0 : Fin 18) 18 _ state hState)

theorem FieldsHeight.localCallback_wordsHeight {i : RationalNestedResourceSystem} {s : ℕ} (h : i.FieldsHeight s) (hs : 2 ≤ s)
    (K : ℕ) (hPrecision : K + 2 ≤ s) (outerBits scalarBits : Fin K → Bool)
    (cursor : i.SamplingState) (hCursor : i.LocalCallbackInvariant s cursor) :
    ((i.machine K outerBits scalarBits).step cursor).WordsHeight (localControlWordHeight s) := by
  cases cursor with
  | source q =>
    change i.LocalStoreInvariant 2 (expressionHeightBudget s 1) q at hCursor
    have hsWords := h.phase_wordsHeight hs q hCursor
    have hp := i.localStoreInvariant_closed 2 (expressionHeightBudget s 1)
      (hs.trans (expressionHeightBudget_ge_input s 1)) h.capacity q hCursor
    rw [expressionHeightBudget_comp] at hp
    unfold machine WordStateMachine.serial serialTransition
    dsimp only
    cases ht : i.phase.step q with
    | done value =>
      rw [ht] at hp
      exact WordTransition.mapState_wordsHeight (fun q => (SerialState.continuation value q : i.SamplingState)) _ _
        (i.continuation_wordsHeight s K outerBits scalarBits value (i.continuationStart K outerBits value)
          (h.continuationStart_bounded hs K hPrecision outerBits value hp))
    | ask a b hb hab upper lower => rw [ht] at hsWords; exact hsWords
  | continuation value state =>
    exact WordTransition.mapState_wordsHeight (fun q => (SerialState.continuation value q : i.SamplingState)) _ _
      (i.continuation_wordsHeight s K outerBits scalarBits value state hCursor.2)

end Blotto.RationalNestedResourceSystem
