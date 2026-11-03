import Blotto.RationalDeferredStoreHeight
import Blotto.RationalNestedResourceCallbackWork
import Blotto.CachedCallbackInitialUnder

/-! Reached local deferred-store and retained-test costs follow the same
joined path. The initial ready event costs zero, so at most two updates pay.
Full resource copying is allowed explicitly; native uniqueness is not assumed. -/

namespace Blotto.RationalNestedResourceSystem

def LocalStoreInvariant (i : RationalNestedResourceSystem) (C s : ℕ) (cursor : i.PhaseCursor) : Prop :=
  rationalLocalStoreInvariant i.capacity C s cursor.1

theorem localStoreInvariant_closed (i : RationalNestedResourceSystem) (C s : ℕ) (hs : 2 ≤ s)
    (hCaps : ∀ j, RationalHeight (i.capacity j) s) : ∀ cursor, i.LocalStoreInvariant C s cursor →
      (i.phase.step cursor).Postcondition (i.LocalStoreInvariant C s)
        (fun value => value.1.resource.HeightAt (expressionHeightBudget s (3 * C))) := by
  intro cursor hCursor
  exact WordTransition.restrict_extraPostcondition i.CursorInvariant (rationalLocalStoreInvariant i.capacity C s)
    i.TerminalState (fun value => value.resource.HeightAt (expressionHeightBudget s (3 * C)))
    ((rationalResourceMachine i.capacity).step cursor.1) (i.phaseProof cursor.1 cursor.2)
    (rationalLocalStoreInvariant_closed i.capacity C s hs hCaps cursor.1 hCursor)

theorem FieldsHeight.localStore_start {i : RationalNestedResourceSystem} {s : ℕ} (h : i.FieldsHeight s) :
    i.LocalStoreInvariant 2 (expressionHeightBudget s 1) i.start := ⟨h.localHeight_start, trivial⟩

theorem FieldsHeight.localStore_closed {i : RationalNestedResourceSystem} {s : ℕ} (h : i.FieldsHeight s)
    (hs : 2 ≤ s) : ∀ cursor, i.LocalStoreInvariant 2 (expressionHeightBudget s 1) cursor →
      (i.phase.step cursor).Postcondition (i.LocalStoreInvariant 2 (expressionHeightBudget s 1)) (fun _ => True) := by
  intro cursor hCursor
  have hp := i.localStoreInvariant_closed 2 _ (hs.trans (expressionHeightBudget_ge_input s 1)) h.capacity cursor hCursor
  cases ht : i.phase.step cursor with
  | done value => trivial
  | ask a b hb hab upper lower => rw [ht] at hp; exact hp

theorem FieldsHeight.localStoreCharge_bound {i : RationalNestedResourceSystem} {s : ℕ} (_h : i.FieldsHeight s)
    (hs : 2 ≤ s) (model : RationalCostModel) (copyResources : Bool) (cursor : i.PhaseCursor)
    (hCursor : i.LocalStoreInvariant 2 (expressionHeightBudget s 1) cursor) :
    rationalResourceStoreBitCharge model copyResources cursor.1 ≤
      (if copyResources then 36 else 32) * model.rat (8 * expressionHeightBudget s 7 + 7) := by
  have hd := hCursor.2
  change rationalDeferredStoreHeight i.capacity (expressionHeightBudget (expressionHeightBudget s 1) 6) cursor.1 at hd
  rw [expressionHeightBudget_comp] at hd
  exact rationalResourceStoreBitCharge_height_bound i.capacity model copyResources _
    (hs.trans (expressionHeightBudget_ge_input s 7)) cursor.1 hd

theorem FieldsHeight.localRetainedCharge_bound {i : RationalNestedResourceSystem} {s : ℕ} (h : i.FieldsHeight s)
    (hs : 2 ≤ s) (model : RationalCostModel) (cursor : i.PhaseCursor)
    (hCursor : i.LocalStoreInvariant 2 (expressionHeightBudget s 1) cursor) :
    rationalResourceRetainedBitCharge model cursor.1 ≤ 10 * model.rat (1 + 2 * expressionHeightBudget s 7) := by
  have hr := rationalResourceHeightInvariant_resource i.capacity 2 (expressionHeightBudget s 1) cursor.1 hCursor.1
  rw [expressionHeightBudget_comp] at hr
  have hCaps := fun j => (h.capacity j).mono (expressionHeightBudget_mono s (by decide : 1 ≤ 7))
  exact rationalResourceRetainedBitCharge_height_bound i.capacity model _
    (hs.trans (expressionHeightBudget_ge_input s 7)) hCaps cursor.1 hr

theorem localZeroInitialWork_bound (i : RationalNestedResourceSystem) (C s : ℕ)
    (hClosed : ∀ cursor, i.LocalStoreInvariant C s cursor →
      (i.phase.step cursor).Postcondition (i.LocalStoreInvariant C s) (fun _ => True))
    (charge : i.PhaseCursor → ℕ) (bound : ℕ) (hCharge : ∀ cursor, i.LocalStoreInvariant C s cursor → charge cursor ≤ bound)
    (hStart : i.LocalStoreInvariant C s i.start) (hZero : charge i.start = 0)
    (K : ℕ) (outerBits scalarBits : Fin K → Bool) (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) :
    (i.machine K outerBits scalarBits).cachedCallbackWork (WordStateMachine.serialSourceCharge charge)
      N bits (.state i.samplingStart) pos hpos ≤ 2 * bound := by
  have he := i.phase.cachedCallbackWork_serialSource (i.continuationMachine K outerBits scalarBits)
    (i.continuationStart K outerBits) 17 (i.continuation_rank K outerBits scalarBits)
    charge N bits (.state i.start) pos hpos
  have hp := i.phase.cachedCallbackWork_state_initial_bound_under (i.LocalStoreInvariant C s)
    hClosed charge bound hCharge N bits i.start hStart hZero pos hpos
  have hTotal := hp.trans (Nat.mul_le_mul_left bound i.phase_rank)
  exact he.le.trans (hTotal.trans_eq (Nat.mul_comm bound 2))

def phaseStoreBitWork (i : RationalNestedResourceSystem) (model : RationalCostModel) (copyResources : Bool) (K : ℕ)
    (outerBits scalarBits : Fin K → Bool) (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) : ℕ :=
  (i.machine K outerBits scalarBits).cachedCallbackWork
    (WordStateMachine.serialSourceCharge (fun cursor : i.PhaseCursor => rationalResourceStoreBitCharge model copyResources cursor.1))
    N bits (.state i.samplingStart) pos hpos

theorem FieldsHeight.phaseStoreBitWork_bound {i : RationalNestedResourceSystem} {s : ℕ} (h : i.FieldsHeight s)
    (hs : 2 ≤ s) (model : RationalCostModel) (copyResources : Bool) (K : ℕ) (outerBits scalarBits : Fin K → Bool)
    (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) :
    i.phaseStoreBitWork model copyResources K outerBits scalarBits N bits pos hpos ≤
      (if copyResources then 72 else 64) * model.rat (8 * expressionHeightBudget s 7 + 7) := by
  have hp := i.localZeroInitialWork_bound 2 (expressionHeightBudget s 1) (h.localStore_closed hs)
    (fun cursor => rationalResourceStoreBitCharge model copyResources cursor.1)
    ((if copyResources then 36 else 32) * model.rat (8 * expressionHeightBudget s 7 + 7))
    (h.localStoreCharge_bound hs model copyResources) h.localStore_start rfl K outerBits scalarBits N bits pos hpos
  change i.phaseStoreBitWork model copyResources K outerBits scalarBits N bits pos hpos ≤ _ at hp
  have hPrice : 2 * ((if copyResources then 36 else 32) * model.rat (8 * expressionHeightBudget s 7 + 7)) =
      (if copyResources then 72 else 64) * model.rat (8 * expressionHeightBudget s 7 + 7) := by cases copyResources <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> ring
  exact hp.trans_eq hPrice

def phaseRetainedBitWork (i : RationalNestedResourceSystem) (model : RationalCostModel) (K : ℕ)
    (outerBits scalarBits : Fin K → Bool) (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) : ℕ :=
  (i.machine K outerBits scalarBits).cachedCallbackWork
    (WordStateMachine.serialSourceCharge (fun cursor : i.PhaseCursor => rationalResourceRetainedBitCharge model cursor.1))
    N bits (.state i.samplingStart) pos hpos

theorem FieldsHeight.phaseRetainedBitWork_bound {i : RationalNestedResourceSystem} {s : ℕ} (h : i.FieldsHeight s)
    (hs : 2 ≤ s) (model : RationalCostModel) (K : ℕ) (outerBits scalarBits : Fin K → Bool)
    (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) :
    i.phaseRetainedBitWork model K outerBits scalarBits N bits pos hpos ≤ 20 * model.rat (1 + 2 * expressionHeightBudget s 7) := by
  have hp := i.localZeroInitialWork_bound 2 (expressionHeightBudget s 1) (h.localStore_closed hs)
    (fun cursor => rationalResourceRetainedBitCharge model cursor.1)
    (10 * model.rat (1 + 2 * expressionHeightBudget s 7)) (h.localRetainedCharge_bound hs model)
    h.localStore_start rfl K outerBits scalarBits N bits pos hpos
  change i.phaseRetainedBitWork model K outerBits scalarBits N bits pos hpos ≤ _ at hp
  have hPrice : 2 * (10 * model.rat (1 + 2 * expressionHeightBudget s 7)) = 20 * model.rat (1 + 2 * expressionHeightBudget s 7) := by ring
  exact hp.trans_eq hPrice

end Blotto.RationalNestedResourceSystem
