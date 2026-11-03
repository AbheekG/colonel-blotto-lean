import Blotto.RationalNestedCombinedLedger

/-! A closed invariant joins retained source-store heights to the actual
18-slot terminal weight list. Uniform callback prices hold only on reached
states; arbitrary unreachable values impose no extra promise. -/

namespace Blotto.RationalNestedResourceSystem

def LocalCallbackInvariant (i : RationalNestedResourceSystem) (s : ℕ) : i.SamplingState → Prop :=
  WordStateMachine.serialHandoffInvariant (i.LocalStoreInvariant 2 (expressionHeightBudget s 1))
    (fun value => value.1.resource.HeightAt (expressionHeightBudget s 7))
    (fun _ state => state.Bounded 18 (expressionHeightBudget s 54))

theorem FieldsHeight.localCallback_start {i : RationalNestedResourceSystem} {s : ℕ} (h : i.FieldsHeight s) :
    i.LocalCallbackInvariant s i.samplingStart := h.localStore_start

theorem FieldsHeight.localCallback_closed {i : RationalNestedResourceSystem} {s : ℕ} (h : i.FieldsHeight s)
    (hs : 2 ≤ s) (K : ℕ) (hPrecision : K + 2 ≤ s) (outerBits scalarBits : Fin K → Bool) :
    ∀ cursor, i.LocalCallbackInvariant s cursor →
      ((i.machine K outerBits scalarBits).step cursor).Postcondition (i.LocalCallbackInvariant s) (fun _ => True) := by
  apply i.phase.serialHandoffInvariant_closed (i.continuationMachine K outerBits scalarBits)
    (i.continuationStart K outerBits) 17 (i.continuation_rank K outerBits scalarBits)
    (i.LocalStoreInvariant 2 (expressionHeightBudget s 1))
    (fun value => value.1.resource.HeightAt (expressionHeightBudget s 7))
    (fun _ state => state.Bounded 18 (expressionHeightBudget s 54))
  · have hp := i.localStoreInvariant_closed 2 (expressionHeightBudget s 1)
      (hs.trans (expressionHeightBudget_ge_input s 1)) h.capacity
    simpa only [expressionHeightBudget_comp] using hp
  · exact fun value hValue => h.continuationStart_bounded hs K hPrecision outerBits value hValue
  · exact fun value _ state hState => i.continuation_bounded_closed _ K outerBits scalarBits value state hState

theorem localCallback_priceWidths (s : ℕ) :
    32 * expressionHeightBudget s 7 + 31 ≤ categoricalRequestWidth 18 (expressionHeightBudget s 54) ∧
      8 * expressionHeightBudget s 7 + 7 ≤ categoricalRequestWidth 18 (expressionHeightBudget s 54) ∧
      1 + 2 * expressionHeightBudget s 7 ≤ categoricalRequestWidth 18 (expressionHeightBudget s 54) := by
  have hm := expressionHeightBudget_mono s (by decide : 7 ≤ 54)
  unfold categoricalRequestWidth
  omega

theorem FieldsHeight.localCallbackBitCharge_bound {i : RationalNestedResourceSystem} {s : ℕ} (h : i.FieldsHeight s)
    (hs : 2 ≤ s) (model : RationalCostModel) (copyResources : Bool) (K : ℕ) (hPrecision : K + 2 ≤ s)
    (outerBits : Fin K → Bool) (cursor : i.SamplingState) (hCursor : i.LocalCallbackInvariant s cursor) :
    i.localCallbackBitCharge model copyResources K outerBits cursor ≤
      (if copyResources then 299 else 295) * model.rat (categoricalRequestWidth 18 (expressionHeightBudget s 54)) := by
  let W := categoricalRequestWidth 18 (expressionHeightBudget s 54)
  have hw := localCallback_priceWidths s
  cases cursor with
  | source q =>
    change i.LocalStoreInvariant 2 (expressionHeightBudget s 1) q at hCursor
    have hRequest := rationalResourcePairRequestCharge_height_bound i.capacity model 2 _
      (hs.trans (expressionHeightBudget_ge_input s 1)) h.capacity q.1 hCursor.1
    rw [expressionHeightBudget_comp] at hRequest
    have hR := hRequest.trans (Nat.mul_le_mul_left 98 (model.monotone hw.1))
    have hS := (h.localStoreCharge_bound hs model copyResources q hCursor).trans
      (Nat.mul_le_mul_left (if copyResources then 36 else 32) (model.monotone hw.2.1))
    have hT := (h.localRetainedCharge_bound hs model q hCursor).trans
      (Nat.mul_le_mul_left 10 (model.monotone hw.2.2))
    change rationalResourcePairRequestCharge model q.1 ≤ 98 * model.rat W at hR
    change rationalResourceStoreBitCharge model copyResources q.1 ≤ (if copyResources then 36 else 32) * model.rat W at hS
    change rationalResourceRetainedBitCharge model q.1 ≤ 10 * model.rat W at hT
    have hHandoff : WordStateMachine.serialHandoffCharge i.phase (i.continuationStart K outerBits) (fun _ => 0)
        (fun _ => categoricalCallbackBitCost model) (.source q) ≤ 155 * model.rat W := by
      have hp := i.localStoreInvariant_closed 2 (expressionHeightBudget s 1)
        (hs.trans (expressionHeightBudget_ge_input s 1)) h.capacity q hCursor
      rw [expressionHeightBudget_comp] at hp
      unfold WordStateMachine.serialHandoffCharge
      dsimp only
      cases ht : i.phase.step q with
      | done value =>
        rw [ht] at hp
        have hb := h.continuationStart_bounded hs K hPrecision outerBits value hp
        simpa only [Nat.zero_add] using categoricalCallbackBitCost_bound model (i.continuationStart K outerBits value) 18 _ hb
      | ask a b hb hab upper lower => exact Nat.zero_le _
    change i.localCallbackBitCharge model copyResources K outerBits (.source q) ≤
      (if copyResources then 299 else 295) * model.rat W
    unfold localCallbackBitCharge
    simp only [WordStateMachine.serialSourceCharge]
    cases copyResources <;> simp only [Bool.false_eq_true, ite_false, ite_true] at hS ⊢ <;> omega
  | continuation value state =>
    change value.1.resource.HeightAt (expressionHeightBudget s 7) ∧ state.Bounded 18 (expressionHeightBudget s 54) at hCursor
    have hp := categoricalCallbackBitCost_bound model state 18 _ hCursor.2
    change i.localCallbackBitCharge model copyResources K outerBits (.continuation value state) ≤ (if copyResources then 299 else 295) * model.rat W
    unfold localCallbackBitCharge
    simp only [WordStateMachine.serialSourceCharge, WordStateMachine.serialHandoffCharge, Nat.zero_add]
    change categoricalCallbackBitCost model state ≤ 155 * model.rat W at hp
    cases copyResources <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> omega

end Blotto.RationalNestedResourceSystem
