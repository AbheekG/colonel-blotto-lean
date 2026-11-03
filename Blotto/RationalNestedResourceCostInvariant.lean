import Blotto.RationalResourceRequestHeightPrice
import Blotto.RationalCategoricalHeight
import Blotto.RationalNestedResourceHeight
import Blotto.WordTransitionAdditionalPost

/-! Reached local resource states and terminal profile weights carry fixed-
round size certificates through the existing hard-budget proof wrappers. -/

namespace Blotto.RationalNestedResourceSystem

def LocalHeightInvariant (i : RationalNestedResourceSystem) (C s : ℕ) (cursor : i.PhaseCursor) : Prop :=
  rationalResourceHeightInvariant i.capacity C s cursor.1

theorem localHeightInvariant_closed (i : RationalNestedResourceSystem) (C s : ℕ) (hs : 2 ≤ s)
    (hCaps : ∀ j, RationalHeight (i.capacity j) s) : ∀ cursor, i.LocalHeightInvariant C s cursor →
      (i.phase.step cursor).Postcondition (i.LocalHeightInvariant C s)
        (fun value => value.1.resource.HeightAt (expressionHeightBudget s (3 * C))) := by
  intro cursor hCursor
  exact WordTransition.restrict_extraPostcondition i.CursorInvariant
    (rationalResourceHeightInvariant i.capacity C s) i.TerminalState
    (fun value => value.resource.HeightAt (expressionHeightBudget s (3 * C)))
    ((rationalResourceMachine i.capacity).step cursor.1) (i.phaseProof cursor.1 cursor.2)
    (rationalResourceHeightInvariant_closed i.capacity C s hs hCaps cursor.1 hCursor)

theorem FieldsHeight.localHeight_start {i : RationalNestedResourceSystem} {s : ℕ} (h : i.FieldsHeight s) :
    i.LocalHeightInvariant 2 (expressionHeightBudget s 1) i.start :=
  rationalResourceHeightInvariant_initial i.capacity i.initial 2 _
    (fun j => (h.2.2.2 j).mono (expressionHeightBudget_ge_input s 1)) i.initial_rank

theorem FieldsHeight.localHeight_closed {i : RationalNestedResourceSystem} {s : ℕ} (h : i.FieldsHeight s)
    (hs : 2 ≤ s) : ∀ cursor, i.LocalHeightInvariant 2 (expressionHeightBudget s 1) cursor →
      (i.phase.step cursor).Postcondition (i.LocalHeightInvariant 2 (expressionHeightBudget s 1))
        (fun value => value.1.resource.HeightAt (expressionHeightBudget s 7)) := by
  have hp := i.localHeightInvariant_closed 2 _ (hs.trans (expressionHeightBudget_ge_input s 1)) h.capacity
  simpa only [expressionHeightBudget_comp] using hp

theorem FieldsHeight.continuationStart_bounded {i : RationalNestedResourceSystem} {s : ℕ} (h : i.FieldsHeight s)
    (hs : 2 ≤ s) (K : ℕ) (hPrecision : K + 2 ≤ s) (outerBits : Fin K → Bool) (value : i.PhaseResult)
    (hValue : value.1.resource.HeightAt (expressionHeightBudget s 7)) :
    (i.continuationStart K outerBits value).Bounded 18 (expressionHeightBudget s 54) := by
  have hProfile := (h.terminalData value hValue).profile (hs.trans (expressionHeightBudget_ge_input s 7)) K outerBits
  rw [max_eq_left (hPrecision.trans (expressionHeightBudget_ge_input s 7)), expressionHeightBudget_comp] at hProfile
  exact rationalWeightList_bounded ((i.terminalData value).profile K outerBits).weight
    ((i.terminalData value).profile K outerBits).nonnegative _ hProfile.1

theorem continuation_bounded_closed (i : RationalNestedResourceSystem) (t K : ℕ)
    (outerBits scalarBits : Fin K → Bool) (value : i.PhaseResult)
    (state : CategoricalState (Fin 18)) (hState : state.Bounded 18 t) :
    ((i.continuationMachine K outerBits scalarBits value).step state).Postcondition
      (fun q => q.Bounded 18 t) (fun _ => True) :=
  WordTransition.mapValue_statePostcondition
    (fun slot => ((i.terminalData value).profile K outerBits).point K slot scalarBits)
    (fun q => q.Bounded 18 t) ((categoricalMachine (0 : Fin 18)).step state)
    (categoricalTransition_bounded (0 : Fin 18) 18 t state hState)

end Blotto.RationalNestedResourceSystem
