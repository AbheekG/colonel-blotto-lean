import Blotto.RationalResourceHeightInvariant
import Blotto.RationalResourceStoreBitPrice
import Blotto.RationalLottoClassificationPrice

/-! Deferred local stores need heights of the retained old array and chosen
endpoint, in addition to the materialized state. Constant-round invariants
preserve both on reached paths. Logical/full copying remain explicit. -/

namespace Blotto

def rationalDeferredStoreHeight {n : ℕ} (L : Fin n → ℚ) (t : ℕ) : RationalResourceCursor L → Prop
  | .ready _ => True
  | .selected state _ _ _ _ z => state.resource.HeightAt t ∧ RationalHeight z t

theorem rationalResourceStep_deferredHeight {n : ℕ} {L : Fin n → ℚ}
    (state : RationalActiveResources L) (C s : ℕ) (hs : 2 ≤ s)
    (hCaps : ∀ j, RationalHeight (L j) s) (hRank : state.active.length - 1 ≤ C)
    (hResource : state.resource.HeightAt (expressionHeightBudget s (3 * (C - (state.active.length - 1))))) :
    (rationalResourceStep state).Postcondition (rationalDeferredStoreHeight L (expressionHeightBudget s (3 * C))) (fun _ => True) := by
  rw [rationalResourceStep_refines]
  cases state with
  | mk resource active hn hm =>
    cases active with
    | nil => trivial
    | cons a rest =>
      cases rest with
      | nil => trivial
      | cons b tail =>
        let state : RationalActiveResources L := ⟨resource, a :: b :: tail, hn, hm⟩
        let d := 3 * (C - (state.active.length - 1))
        have hPair : (state.pair a b tail rfl).FieldsHeight (expressionHeightBudget s d) :=
          ⟨(hCaps a).mono (expressionHeightBudget_ge_input s d), (hCaps b).mono (expressionHeightBudget_ge_input s d), hResource a, hResource b⟩
        have hEndpoints := hPair.endpoints (hs.trans (expressionHeightBudget_ge_input s d))
        rw [expressionHeightBudget_comp] at hEndpoints
        have hOld : resource.HeightAt (expressionHeightBudget s (3 * C)) :=
          hResource.mono (expressionHeightBudget_mono s (by dsimp [d]; omega))
        have hEnd : d + 2 ≤ 3 * C := by
          have hLen : 2 ≤ state.active.length := by simp [state]
          have hRank' : state.active.length - 1 ≤ C := hRank
          dsimp [d]
          omega
        exact ⟨⟨hOld, hEndpoints.2.mono (expressionHeightBudget_mono s hEnd)⟩,
          ⟨hOld, hEndpoints.1.mono (expressionHeightBudget_mono s hEnd)⟩⟩

def rationalLocalStoreInvariant {n : ℕ} (L : Fin n → ℚ) (C s : ℕ) (cursor : RationalResourceCursor L) : Prop :=
  rationalResourceHeightInvariant L C s cursor ∧ rationalDeferredStoreHeight L (expressionHeightBudget s (3 * C)) cursor

theorem rationalLocalStoreInvariant_closed {n : ℕ} (L : Fin n → ℚ) (C s : ℕ) (hs : 2 ≤ s)
    (hCaps : ∀ j, RationalHeight (L j) s) : ∀ cursor, rationalLocalStoreInvariant L C s cursor →
      ((rationalResourceMachine L).step cursor).Postcondition (rationalLocalStoreInvariant L C s)
        (fun value => value.resource.HeightAt (expressionHeightBudget s (3 * C))) := by
  intro cursor hCursor
  have hBase := rationalResourceHeightInvariant_closed L C s hs hCaps cursor hCursor.1
  have hStore := rationalResourceStep_deferredHeight cursor.materialize C s hs hCaps hCursor.1.1 hCursor.1.2
  change ((rationalResourceMachine L).step cursor).Postcondition
    (rationalDeferredStoreHeight L (expressionHeightBudget s (3 * C))) (fun _ => True) at hStore
  cases ht : (rationalResourceMachine L).step cursor with
  | done value => rw [ht] at hBase; exact hBase
  | ask a b hb hab upper lower =>
    rw [ht] at hBase hStore
    exact ⟨⟨hBase.1, hStore.1⟩, ⟨hBase.2, hStore.2⟩⟩

theorem rationalResourceStoreBitCharge_height_bound {n : ℕ} (L : Fin n → ℚ) (model : RationalCostModel)
    (copyResources : Bool) (t : ℕ) (ht : 2 ≤ t) (cursor : RationalResourceCursor L)
    (h : rationalDeferredStoreHeight L t cursor) :
    rationalResourceStoreBitCharge model copyResources cursor ≤ (if copyResources then 2 * n + 30 else 32) * model.rat (8 * t + 7) := by
  cases cursor with
  | ready state => exact Nat.zero_le _
  | selected state a b tail he z =>
    exact PairStoreProgram.updateBitCost_bound model copyResources
      (⟨state.resource.data, state.resource.size⟩ : PairStoreBuffer n ℚ) a b z t ht h.1 h.2

theorem rationalResourceRetainedBitCharge_height_bound {n : ℕ} (L : Fin n → ℚ) (model : RationalCostModel)
    (t : ℕ) (ht : 2 ≤ t) (hCaps : ∀ j, RationalHeight (L j) t) (cursor : RationalResourceCursor L)
    (h : cursor.materialize.resource.HeightAt t) :
    rationalResourceRetainedBitCharge model cursor ≤ 10 * model.rat (1 + 2 * t) := by
  have hZero : rationalWordWidth (0 : ℚ) ≤ 1 + 2 * t := by
    have hz : rationalWordWidth (0 : ℚ) = 3 := by decide
    omega
  have hL := fun j => rationalWordWidth_of_height (hCaps j)
  have hR := fun j => rationalWordWidth_of_height (h j)
  cases cursor with
  | ready state => exact Nat.zero_le _
  | selected state a b tail he z =>
    exact rationalRetainedFractionalBitCost_bound model L (state.update a b tail he z).resource a b _ hZero hL hR

end Blotto
