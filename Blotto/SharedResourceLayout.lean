import Blotto.SharedResourceCursor

/-! Logical persistent payload bounds for the one-state cursor. There is one
resource array and no successor-state pair. These value-layout counts are not
native reference-count or allocator/peak-space certificates. -/

namespace Blotto.RationalActiveResources

theorem active_length_le {n : ℕ} {L : Fin n → ℚ} (state : RationalActiveResources L) : state.active.length ≤ n := by
  have hEq := state.realView.length_eq_card
  change state.active.length = (fractionalSet (fun j => (L j : ℝ)) state.resource.realAllocation).card at hEq
  have hCard := Finset.card_le_univ (s := fractionalSet (fun j => (L j : ℝ)) state.resource.realAllocation)
  rw [← hEq] at hCard
  simpa only [Fintype.card_fin] using hCard

end Blotto.RationalActiveResources
namespace Blotto.SharedResourceCursor

def retainedState {n : ℕ} {L : Fin n → ℚ} : SharedResourceCursor L → RationalActiveResources L
  | .ready state => state
  | .coin choice _ _ _ _ => choice.state

def resourceRegionCount {n : ℕ} {L : Fin n → ℚ} (_cursor : SharedResourceCursor L) : ℕ := 1

def resourceCellCount {n : ℕ} {L : Fin n → ℚ} (cursor : SharedResourceCursor L) : ℕ :=
  cursor.retainedState.resource.data.size

theorem resource_layout {n : ℕ} {L : Fin n → ℚ} (cursor : SharedResourceCursor L) :
    cursor.resourceRegionCount = 1 ∧ cursor.resourceCellCount = n :=
  ⟨rfl, cursor.retainedState.resource.size⟩

def retainedIndexSlots {n : ℕ} {L : Fin n → ℚ} (cursor : SharedResourceCursor L) : ℕ :=
  cursor.retainedState.active.length + match cursor with
    | .ready _ => 0
    | .coin choice _ _ _ _ => choice.tail.length + 2

theorem retainedIndexSlots_bound {n : ℕ} {L : Fin n → ℚ} (cursor : SharedResourceCursor L) :
    cursor.retainedIndexSlots ≤ 2 * n := by
  cases cursor with
  | ready state =>
    have h := state.active_length_le
    change state.active.length + 0 ≤ 2 * n
    omega
  | coin choice a b hb hab =>
    have h := choice.state.active_length_le
    have hHead := congrArg List.length choice.head_pair
    simp only [List.length_cons] at hHead
    change choice.state.active.length + (choice.tail.length + 2) ≤ 2 * n
    omega

def endpointSlots {n : ℕ} {L : Fin n → ℚ} : SharedResourceCursor L → ℕ
  | .ready _ => 0
  | .coin _ _ _ _ _ => 2

theorem endpointSlots_bound {n : ℕ} {L : Fin n → ℚ} (cursor : SharedResourceCursor L) : cursor.endpointSlots ≤ 2 := by
  cases cursor <;> simp [endpointSlots]

def booleanCells {n : ℕ} {L : Fin n → ℚ} : SharedResourceCursor L → ℕ
  | .ready _ => 0
  | @SharedResourceCursor.coin _ _ w _ _ _ _ _ => 2 * w

theorem prepared_booleanCells {n : ℕ} {L : Fin n → ℚ} (p : PreparedResourceChoice L) :
    (prepared p).booleanCells = 2 * binaryWordWidth p.words.denominator := rfl

end Blotto.SharedResourceCursor
