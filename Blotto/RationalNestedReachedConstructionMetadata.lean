import Blotto.RationalNestedFactoryMetadata
import Blotto.RationalNestedReachedDataCharge

/-! Reached local callbacks have a complete terminal-construction metadata
price bound. Source/continuation invariants are retained; unreachable prices
are not clipped or assumed bounded. -/

namespace Blotto.RationalNestedResourceSystem

def localConstructionMetadataCharge (i : RationalNestedResourceSystem) (primitive : ℕ → ℕ) (c K : ℕ)
    (outerBits : Fin K → Bool) (cursor : i.SamplingState) : ℕ :=
  WordStateMachine.serialFactoryCharge i.phase (i.continuationStart K outerBits)
    (i.terminalConstructionMetadataPrice primitive c K outerBits) cursor

theorem FieldsHeight.localConstructionMetadataCharge_bound {i : RationalNestedResourceSystem} {s : ℕ}
    (h : i.FieldsHeight s) (hs : 2 ≤ s) (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w)
    (K : ℕ) (hK : K + 2 ≤ s) (outerBits : Fin K → Bool) (cursor : i.SamplingState) (hCursor : i.LocalCallbackInvariant s cursor) :
    i.localConstructionMetadataCharge primitive c K outerBits cursor ≤
      2 * RationalTerminalResources.profileConstructionMetadataBound c (expressionHeightBudget s 7) K := by
  let I := i.LocalStoreInvariant 2 (expressionHeightBudget s 1)
  let P := fun value : i.PhaseResult => value.1.resource.HeightAt (expressionHeightBudget s 7)
  let J := fun (_ : i.PhaseResult) (state : CategoricalState (Fin 18)) => state.Bounded 18 (expressionHeightBudget s 54)
  have hSource : ∀ state, I state → (i.phase.step state).Postcondition I P := by
    have hp := i.localStoreInvariant_closed 2 _ (hs.trans (expressionHeightBudget_ge_input s 1)) h.capacity
    simpa only [expressionHeightBudget_comp] using hp
  exact i.phase.serialFactoryCharge_bound_under (i.continuationStart K outerBits) I P J hSource
    (i.terminalConstructionMetadataPrice primitive c K outerBits)
    (RationalTerminalResources.profileConstructionMetadataBound c (expressionHeightBudget s 7) K)
    (fun value hValue => h.terminalConstructionMetadataPrice_bound hs primitive c hPrimitive K hK outerBits value hValue)
    cursor hCursor

end Blotto.RationalNestedResourceSystem
