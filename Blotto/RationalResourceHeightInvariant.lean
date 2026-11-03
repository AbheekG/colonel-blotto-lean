import Blotto.RationalResourceHeight

/-! Rank-indexed heights bound every reached local resource state, not only
terminal leaves. The fixed-round bound is for constant-size local phases;
the general n-coordinate PRG loop retains its independent lattice bound. -/

namespace Blotto

def rationalResourceHeightInvariant {n : ℕ} (L : Fin n → ℚ) (C s : ℕ) (cursor : RationalResourceCursor L) : Prop :=
  (rationalResourceMachine L).rank cursor ≤ C ∧
    cursor.materialize.resource.HeightAt (expressionHeightBudget s (3 * (C - (rationalResourceMachine L).rank cursor)))

theorem rationalResourceHeightInvariant_closed {n : ℕ} (L : Fin n → ℚ) (C s : ℕ) (hs : 2 ≤ s)
    (hL : ∀ j, RationalHeight (L j) s) : ∀ cursor, rationalResourceHeightInvariant L C s cursor →
      ((rationalResourceMachine L).step cursor).Postcondition (rationalResourceHeightInvariant L C s)
        (fun value => value.resource.HeightAt (expressionHeightBudget s (3 * C))) := by
  intro cursor hCursor
  let depth := 3 * (C - (rationalResourceMachine L).rank cursor)
  have hsD : 2 ≤ expressionHeightBudget s depth := hs.trans (expressionHeightBudget_ge_input s depth)
  have hCaps := fun j => (hL j).mono (expressionHeightBudget_ge_input s depth)
  have hStep := rationalResourceStep_height cursor.materialize _ hsD hCaps hCursor.2
  change (match (rationalResourceMachine L).step cursor with
    | .done value => value.resource.HeightAt (expressionHeightBudget s depth)
    | .ask _ _ _ _ upper lower =>
      upper.materialize.resource.HeightAt (expressionHeightBudget (expressionHeightBudget s depth) 3) ∧
      lower.materialize.resource.HeightAt (expressionHeightBudget (expressionHeightBudget s depth) 3)) at hStep
  cases ht : (rationalResourceMachine L).step cursor with
  | done value =>
    rw [ht] at hStep
    exact hStep.mono (expressionHeightBudget_mono s (by dsimp [depth]; omega))
  | ask a b hb hab upper lower =>
    have hp := (rationalResourceMachine L).progress cursor
    rw [ht] at hp hStep
    rw [expressionHeightBudget_comp] at hStep
    have hC := hCursor.1
    have hUpper : depth + 3 ≤ 3 * (C - (rationalResourceMachine L).rank upper) := by dsimp [depth]; omega
    have hLower : depth + 3 ≤ 3 * (C - (rationalResourceMachine L).rank lower) := by dsimp [depth]; omega
    exact ⟨⟨by omega, hStep.1.mono (expressionHeightBudget_mono s hUpper)⟩,
      ⟨by omega, hStep.2.mono (expressionHeightBudget_mono s hLower)⟩⟩

theorem rationalResourceHeightInvariant_initial {n : ℕ} (L r : Fin n → ℚ) (C s : ℕ)
    (hR : ∀ j, RationalHeight (r j) s)
    (hRank : (rationalResourceMachine L).rank (.ready (RationalActiveResources.initial L r)) ≤ C) :
    rationalResourceHeightInvariant L C s (.ready (RationalActiveResources.initial L r)) := by
  refine ⟨hRank, ?_⟩
  intro j
  change RationalHeight ((RationalResourceArray.ofAllocation r).allocation j) _
  rw [RationalResourceArray.allocation_ofAllocation]
  exact (hR j).mono (expressionHeightBudget_ge_input s _)

theorem rationalResourceHeightInvariant_resource {n : ℕ} (L : Fin n → ℚ) (C s : ℕ)
    (cursor : RationalResourceCursor L) (h : rationalResourceHeightInvariant L C s cursor) :
    cursor.materialize.resource.HeightAt (expressionHeightBudget s (3 * C)) :=
  h.2.mono (expressionHeightBudget_mono s (by omega))

end Blotto
