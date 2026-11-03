import Blotto.RationalResourcePairBitPrice

/-! Reached deferred cursors retain a unit-box old array on the input lattice
and one of the pair endpoints. This certifies the operands used before the
selected update, not merely its final materialized resource state. -/

namespace Blotto.RationalActiveResources

def UnitResources {n : ℕ} {L : Fin n → ℚ} (state : RationalActiveResources L) : Prop :=
  ∀ j, 0 ≤ state.resource.allocation j ∧ state.resource.allocation j ≤ 1

theorem update_unitResources {n : ℕ} {L : Fin n → ℚ} (state : RationalActiveResources L)
    (hUnit : state.UnitResources) (hL : ∀ j, L j ≤ 1)
    (a b : Fin n) (tail : List (Fin n)) (he : state.active = a :: b :: tail) (z : ℚ)
    (hz : z = (state.pair a b tail he).lower ∨ z = (state.pair a b tail he).upper) :
    (state.update a b tail he z).UnitResources := by
  have hBox := (state.pair a b tail he).branch_feasible hz
  intro j
  change 0 ≤ (state.resource.updatePair a b z).allocation j ∧ (state.resource.updatePair a b z).allocation j ≤ 1
  rw [RationalResourceArray.allocation_updatePair]
  simp only [Function.update_apply]
  split_ifs
  · exact ⟨hBox.2.2.1, hBox.2.2.2.trans (hL b)⟩
  · exact ⟨hBox.1, hBox.2.1.trans (hL a)⟩
  · exact hUnit j

end Blotto.RationalActiveResources
namespace Blotto

def rationalResourceStoreInvariant {n : ℕ} (L : Fin n → ℚ) (D : ℕ) : RationalResourceCursor L → Prop
  | .ready state => state.resource.OnLattice D ∧ state.UnitResources
  | .selected state a b tail he z =>
    (state.resource.OnLattice D ∧ state.UnitResources) ∧
      (z = (state.pair a b tail he).lower ∨ z = (state.pair a b tail he).upper)

theorem rationalResourceStoreInvariant_materialize {n : ℕ} (L : Fin n → ℚ) (D : ℕ)
    (hL : ∀ j, OnRationalLattice D (L j)) (hUnit : ∀ j, L j ≤ 1)
    (cursor : RationalResourceCursor L) (hCursor : rationalResourceStoreInvariant L D cursor) :
    cursor.materialize.resource.OnLattice D ∧ cursor.materialize.UnitResources := by
  cases cursor with
  | ready state => exact hCursor
  | selected state a b tail he z =>
    rcases hCursor with ⟨hOld, hz⟩
    exact ⟨state.update_on_lattice hL hOld.1 a b tail he hz,
      state.update_unitResources hOld.2 hUnit a b tail he z hz⟩

theorem rationalResourceStoreInvariant_closed {n : ℕ} (L : Fin n → ℚ) (D : ℕ)
    (hL : ∀ j, OnRationalLattice D (L j)) (hUnit : ∀ j, L j ≤ 1) :
    ∀ cursor, rationalResourceStoreInvariant L D cursor →
      ((rationalResourceMachine L).step cursor).Postcondition (rationalResourceStoreInvariant L D) (fun _ => True) := by
  intro cursor hCursor
  have hMat := rationalResourceStoreInvariant_materialize L D hL hUnit cursor hCursor
  unfold rationalResourceMachine rationalResourceTransition
  dsimp only
  rw [rationalResourceStep_refines]
  cases hState : cursor.materialize with
  | mk resource active hn hm =>
    rw [hState] at hMat
    cases active with
    | nil => trivial
    | cons a rest =>
      cases rest with
      | nil => trivial
      | cons b tail => exact ⟨⟨hMat, Or.inr rfl⟩, ⟨hMat, Or.inl rfl⟩⟩

theorem rationalResourceStoreInvariant_initial {n : ℕ} (L r : Fin n → ℚ) (D : ℕ)
    (hR : ∀ j, OnRationalLattice D (r j)) (hUnit : ∀ j, 0 ≤ r j ∧ r j ≤ 1) :
    rationalResourceStoreInvariant L D (.ready (RationalActiveResources.initial L r)) := by
  constructor
  · exact rationalResourcePairInvariant_initial L r D hR
  · intro j
    change 0 ≤ (RationalResourceArray.ofAllocation r).allocation j ∧ (RationalResourceArray.ofAllocation r).allocation j ≤ 1
    rw [RationalResourceArray.allocation_ofAllocation]
    exact hUnit j

end Blotto
