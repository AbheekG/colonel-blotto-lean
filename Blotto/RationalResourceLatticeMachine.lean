import Blotto.RationalResourceLattice

/-! The concrete resource controller preserves the input denominator on
all completed bit paths and all ideal leaves, including deferred updates. -/

namespace Blotto

theorem rationalResourceStep_lattice {n : ℕ} {L : Fin n → ℚ} (D : ℕ)
    (hL : ∀ j, OnRationalLattice D (L j)) (s : RationalActiveResources L) (hs : s.resource.OnLattice D) :
    match rationalResourceStep s with
    | .done value => value.resource.OnLattice D
    | .ask _ _ _ _ upper lower => upper.materialize.resource.OnLattice D ∧ lower.materialize.resource.OnLattice D := by
  cases s with
  | mk resource active hn hm =>
    cases active with
    | nil => exact hs
    | cons a rest =>
      cases rest with
      | nil => exact hs
      | cons b tail =>
        let s : RationalActiveResources L := ⟨resource, a :: b :: tail, hn, hm⟩
        let p := s.pair a b tail rfl
        exact ⟨s.update_on_lattice hL hs a b tail rfl (Or.inr rfl : p.upper = p.lower ∨ p.upper = p.upper),
          s.update_on_lattice hL hs a b tail rfl (Or.inl rfl : p.lower = p.lower ∨ p.lower = p.upper)⟩

theorem rationalResourceMachine_lattice_completed {n : ℕ} (L : Fin n → ℚ) (D : ℕ)
    (hL : ∀ j, OnRationalLattice D (L j)) (cursor : RationalResourceCursor L)
    (R : ℕ) (bits : Fin R → Bool) (hs : cursor.materialize.resource.OnLattice D)
    {result : RationalActiveResources L} (hr : ((rationalResourceMachine L).run R cursor bits).1 = some result) :
    result.resource.OnLattice D := by
  apply (rationalResourceMachine L).accepted_invariant R cursor bits
    (fun c => c.materialize.resource.OnLattice D) (fun s => s.resource.OnLattice D) _ hs hr
  intro c hc
  have hp := rationalResourceStep_lattice D hL c.materialize hc
  unfold rationalResourceMachine rationalResourceTransition
  dsimp only
  cases he : rationalResourceStep c.materialize with
  | done value => rw [he] at hp; exact hp
  | ask a b hb hab upper lower => rw [he] at hp; exact hp

theorem rationalResourceMachine_lattice_leaves {n : ℕ} (L : Fin n → ℚ) (D : ℕ)
    (hL : ∀ j, OnRationalLattice D (L j)) (cursor : RationalResourceCursor L)
    (hs : cursor.materialize.resource.OnLattice D) :
    ((rationalResourceMachine L).specification cursor).decode.ForLeaves (fun s => s.resource.OnLattice D) := by
  apply (rationalResourceMachine L).specification_forLeaves
    (fun c => c.materialize.resource.OnLattice D) (fun s => s.resource.OnLattice D) _ cursor hs
  intro c hc
  have hp := rationalResourceStep_lattice D hL c.materialize hc
  unfold rationalResourceMachine rationalResourceTransition
  dsimp only
  cases he : rationalResourceStep c.materialize with
  | done value => rw [he] at hp; exact hp
  | ask a b hb hab upper lower => rw [he] at hp; exact hp

end Blotto
