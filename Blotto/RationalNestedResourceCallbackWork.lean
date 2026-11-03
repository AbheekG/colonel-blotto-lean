import Blotto.RationalNestedResourceCostInvariant
import Blotto.CachedSerialTerminalWork
import Blotto.CachedSerialSourceEquality
import Blotto.RationalCategoricalCallbackWork

/-! Both components follow the local serial controller at its current reader
position. Source pair/field prices use at most two update rounds; terminal
categorical prices use only the 18-slot continuation rank. Factories, selected
stores/readers, Boolean control, reflection/output and backend remain separate. -/

namespace Blotto.RationalNestedResourceSystem

def phaseRequestBitWork (i : RationalNestedResourceSystem) (model : RationalCostModel) (K : ℕ)
    (outerBits scalarBits : Fin K → Bool) (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) : ℕ :=
  (i.machine K outerBits scalarBits).cachedCallbackWork
    (WordStateMachine.serialSourceCharge (fun cursor : i.PhaseCursor => rationalResourcePairRequestCharge model cursor.1))
    N bits (.state i.samplingStart) pos hpos

theorem FieldsHeight.phaseRequestBitWork_bound {i : RationalNestedResourceSystem} {s : ℕ} (h : i.FieldsHeight s)
    (hs : 2 ≤ s) (model : RationalCostModel) (K : ℕ) (outerBits scalarBits : Fin K → Bool)
    (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) :
    i.phaseRequestBitWork model K outerBits scalarBits N bits pos hpos ≤
      294 * model.rat (32 * expressionHeightBudget s 7 + 31) := by
  let charge := fun cursor : i.PhaseCursor => rationalResourcePairRequestCharge model cursor.1
  let bound := 98 * model.rat (32 * expressionHeightBudget s 7 + 31)
  have hClosed : ∀ cursor, i.LocalHeightInvariant 2 (expressionHeightBudget s 1) cursor →
      (i.phase.step cursor).Postcondition (i.LocalHeightInvariant 2 (expressionHeightBudget s 1)) (fun _ => True) := by
    intro cursor hCursor
    have hp := h.localHeight_closed hs cursor hCursor
    cases ht : i.phase.step cursor with
    | done value => trivial
    | ask a b hb hab upper lower => rw [ht] at hp; exact hp
  have hCharge : ∀ cursor, i.LocalHeightInvariant 2 (expressionHeightBudget s 1) cursor → charge cursor ≤ bound := by
    intro cursor hCursor
    have hp := rationalResourcePairRequestCharge_height_bound i.capacity model 2 _
      (hs.trans (expressionHeightBudget_ge_input s 1)) h.capacity cursor.1 hCursor
    simpa only [expressionHeightBudget_comp] using hp
  have hp := i.phase.cachedCallbackWork_state_bound_under
    (i.LocalHeightInvariant 2 (expressionHeightBudget s 1)) hClosed charge bound hCharge
    N bits i.start h.localHeight_start pos hpos
  have he := i.phase.cachedCallbackWork_serialSource (i.continuationMachine K outerBits scalarBits)
    (i.continuationStart K outerBits) 17 (i.continuation_rank K outerBits scalarBits)
    charge N bits (.state i.start) pos hpos
  change i.phaseRequestBitWork model K outerBits scalarBits N bits pos hpos =
    i.phase.cachedCallbackWork charge N bits (.state i.start) pos hpos at he
  have hRank : i.phase.rank i.start + 1 ≤ 3 := by have hr := i.phase_rank; omega
  have hTotal := hp.trans (Nat.mul_le_mul_left bound hRank)
  rw [← he] at hTotal
  have hPrice : bound * 3 = 294 * model.rat (32 * expressionHeightBudget s 7 + 31) := by dsimp [bound]; ring
  exact hTotal.trans_eq hPrice

def terminalCategoricalBitWork (i : RationalNestedResourceSystem) (model : RationalCostModel) (K : ℕ)
    (outerBits scalarBits : Fin K → Bool) (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) : ℕ :=
  (i.machine K outerBits scalarBits).cachedCallbackWork
    (WordStateMachine.serialHandoffCharge i.phase (i.continuationStart K outerBits) (fun _ => 0)
      (fun _ => categoricalCallbackBitCost model)) N bits (.state i.samplingStart) pos hpos

theorem FieldsHeight.terminalCategoricalBitWork_bound {i : RationalNestedResourceSystem} {s : ℕ} (h : i.FieldsHeight s)
    (hs : 2 ≤ s) (model : RationalCostModel) (K : ℕ) (hPrecision : K + 2 ≤ s) (outerBits scalarBits : Fin K → Bool)
    (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) :
    i.terminalCategoricalBitWork model K outerBits scalarBits N bits pos hpos ≤
      2790 * model.rat (categoricalRequestWidth 18 (expressionHeightBudget s 54)) := by
  have hp := i.phase.cachedSerialTerminalWork_bound_under
    (i.continuationMachine K outerBits scalarBits) (i.continuationStart K outerBits) 17
    (i.continuation_rank K outerBits scalarBits)
    (i.LocalHeightInvariant 2 (expressionHeightBudget s 1))
    (fun value => value.1.resource.HeightAt (expressionHeightBudget s 7))
    (fun _ state => state.Bounded 18 (expressionHeightBudget s 54))
    (h.localHeight_closed hs)
    (fun value hValue => h.continuationStart_bounded hs K hPrecision outerBits value hValue)
    (fun value _ state hState => i.continuation_bounded_closed _ K outerBits scalarBits value state hState)
    (fun _ => categoricalCallbackBitCost model)
    (155 * model.rat (categoricalRequestWidth 18 (expressionHeightBudget s 54)))
    (fun _ _ state hState => categoricalCallbackBitCost_bound model state 18 _ hState)
    N bits i.start h.localHeight_start pos hpos
  change i.terminalCategoricalBitWork model K outerBits scalarBits N bits pos hpos ≤
    (155 * model.rat (categoricalRequestWidth 18 (expressionHeightBudget s 54))) * 18 at hp
  have hPrice : (155 * model.rat (categoricalRequestWidth 18 (expressionHeightBudget s 54))) * 18 =
      2790 * model.rat (categoricalRequestWidth 18 (expressionHeightBudget s 54)) := by ring
  exact hp.trans_eq hPrice

def terminalCategoricalArithmeticWork (i : RationalNestedResourceSystem) (K : ℕ)
    (outerBits scalarBits : Fin K → Bool) (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) : ℕ :=
  (i.machine K outerBits scalarBits).cachedCallbackWork
    (WordStateMachine.serialHandoffCharge i.phase (i.continuationStart K outerBits) (fun _ => 0)
      (fun _ => categoricalCallbackArithmeticWork)) N bits (.state i.samplingStart) pos hpos

theorem FieldsHeight.terminalCategoricalArithmeticWork_bound {i : RationalNestedResourceSystem} {s : ℕ} (h : i.FieldsHeight s)
    (hs : 2 ≤ s) (K : ℕ) (hPrecision : K + 2 ≤ s) (outerBits scalarBits : Fin K → Bool)
    (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) :
    i.terminalCategoricalArithmeticWork K outerBits scalarBits N bits pos hpos ≤ 684 :=
  i.phase.cachedSerialTerminalWork_bound_under
    (i.continuationMachine K outerBits scalarBits) (i.continuationStart K outerBits) 17
    (i.continuation_rank K outerBits scalarBits)
    (i.LocalHeightInvariant 2 (expressionHeightBudget s 1))
    (fun value => value.1.resource.HeightAt (expressionHeightBudget s 7))
    (fun _ state => state.Bounded 18 (expressionHeightBudget s 54))
    (h.localHeight_closed hs)
    (fun value hValue => h.continuationStart_bounded hs K hPrecision outerBits value hValue)
    (fun value _ state hState => i.continuation_bounded_closed _ K outerBits scalarBits value state hState)
    (fun _ => categoricalCallbackArithmeticWork) 38
    (fun _ _ state hState => categoricalCallbackArithmeticWork_bound state 18 _ hState)
    N bits i.start h.localHeight_start pos hpos

end Blotto.RationalNestedResourceSystem
