import Blotto.RationalNestedControlWords

/-! Any reached local done transition exposes a bounded whole vector, not
only outputs reachable from a fresh start. This supports nested map prices
inside an enclosing binary controller without resetting the input reader. -/

namespace Blotto.RationalNestedResourceSystem

theorem FieldsHeight.continuationOutputHeight_post {i : RationalNestedResourceSystem} {s : ℕ}
    (h : i.FieldsHeight s) (hs : 2 ≤ s) (K : ℕ) (hPrecision : K + 2 ≤ s)
    (outerBits scalarBits : Fin K → Bool) (value : i.PhaseResult)
    (hValue : value.1.resource.HeightAt (expressionHeightBudget s 7)) (state : CategoricalState (Fin 18)) :
    match (i.continuationMachine K outerBits scalarBits value).step state with
    | .done x => ∀ j, RationalHeight (x j) (expressionHeightBudget s 57)
    | .ask _ _ _ _ _ _ => True := by
  unfold continuationMachine RationalSegmentLottery.machine WordStateMachine.mapped
  dsimp only
  cases ht : (categoricalMachine (0 : Fin 18)).step state with
  | done slot =>
    intro j
    have hp := (h.terminalData value hValue).point (hs.trans (expressionHeightBudget_ge_input s 7))
      K outerBits scalarBits slot j
    rw [max_eq_left (hPrecision.trans (expressionHeightBudget_ge_input s 7)), expressionHeightBudget_comp] at hp
    exact hp
  | ask a b hb hab upper lower => trivial

theorem FieldsHeight.localOutputHeight_post {i : RationalNestedResourceSystem} {s : ℕ}
    (h : i.FieldsHeight s) (hs : 2 ≤ s) (K : ℕ) (hPrecision : K + 2 ≤ s)
    (outerBits scalarBits : Fin K → Bool) (cursor : i.SamplingState) (hCursor : i.LocalCallbackInvariant s cursor) :
    match (i.machine K outerBits scalarBits).step cursor with
    | .done x => ∀ j, RationalHeight (x j) (expressionHeightBudget s 57)
    | .ask _ _ _ _ _ _ => True := by
  cases cursor with
  | source state =>
    have hp := i.localStoreInvariant_closed 2 (expressionHeightBudget s 1)
      (hs.trans (expressionHeightBudget_ge_input s 1)) h.capacity state hCursor
    rw [expressionHeightBudget_comp] at hp
    unfold machine WordStateMachine.serial serialTransition
    dsimp only
    cases ht : i.phase.step state with
    | done value =>
      rw [ht] at hp
      dsimp only
      have hOutput := h.continuationOutputHeight_post hs K hPrecision outerBits scalarBits value hp (i.continuationStart K outerBits value)
      cases hn : (i.continuationMachine K outerBits scalarBits value).step (i.continuationStart K outerBits value) with
      | done x =>
        rw [hn] at hOutput
        simpa only [WordTransition.mapState] using hOutput
      | ask a b hb hab upper lower => simp only [WordTransition.mapState]
    | ask a b hb hab upper lower => trivial
  | continuation value state =>
    have hOutput := h.continuationOutputHeight_post hs K hPrecision outerBits scalarBits value hCursor.1 state
    unfold machine WordStateMachine.serial serialTransition
    dsimp only
    cases ht : (i.continuationMachine K outerBits scalarBits value).step state with
    | done x => rw [ht] at hOutput; exact hOutput
    | ask a b hb hab upper lower => trivial

end Blotto.RationalNestedResourceSystem
