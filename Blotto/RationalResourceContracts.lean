import Blotto.RationalResourceMachine

/-! The concrete resource phase preserves its exact total and coordinate
box on every completed bit path, and leaves at most one fractional coordinate.
Exhaustion is propagated as none for the eventual whole-player fallback. -/

namespace Blotto
open scoped BigOperators

def RationalResourceInvariant {n : ℕ} (L : Fin n → ℚ) (total : ℝ) (s : RationalActiveResources L) : Prop :=
  InBox (fun j => (L j : ℝ)) s.resource.realAllocation ∧ (∑ j, s.resource.realAllocation j) = total

theorem rationalResourceStep_invariant {n : ℕ} {L : Fin n → ℚ} (total : ℝ) (s : RationalActiveResources L)
    (hs : RationalResourceInvariant L total s) :
    match rationalResourceStep s with
    | .done value => RationalResourceInvariant L total value
    | .ask _ _ _ _ upper lower => RationalResourceInvariant L total upper.materialize ∧
        RationalResourceInvariant L total lower.materialize := by
  rw [rationalResourceStep_refines]
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
        have hu := s.update_inBox a b tail rfl hs.1 (Or.inr rfl : p.upper = p.lower ∨ p.upper = p.upper)
        have hl := s.update_inBox a b tail rfl hs.1 (Or.inl rfl : p.lower = p.lower ∨ p.lower = p.upper)
        have hus := (s.update_sum a b tail rfl p.upper).trans hs.2
        have hls := (s.update_sum a b tail rfl p.lower).trans hs.2
        exact ⟨⟨hu, hus⟩, ⟨hl, hls⟩⟩

theorem rationalResourceMachine_invariant {n : ℕ} (L : Fin n → ℚ) (total : ℝ) (cursor : RationalResourceCursor L)
    (R : ℕ) (bits : Fin R → Bool) (hs : RationalResourceInvariant L total cursor.materialize)
    {result : RationalActiveResources L} (hr : ((rationalResourceMachine L).run R cursor bits).1 = some result) :
    RationalResourceInvariant L total result := by
  apply (rationalResourceMachine L).accepted_invariant R cursor bits
    (fun c => RationalResourceInvariant L total c.materialize) (RationalResourceInvariant L total) _ hs hr
  intro c hc
  have hp := rationalResourceStep_invariant total c.materialize hc
  unfold rationalResourceMachine rationalResourceTransition
  dsimp only
  cases he : rationalResourceStep c.materialize with
  | done value => rw [he] at hp; exact hp
  | ask a b hb hab upper lower => rw [he] at hp; exact hp

theorem rationalResourceMachine_terminal_contract {n : ℕ} (L : Fin n → ℚ) (total : ℝ) (cursor : RationalResourceCursor L)
    (R : ℕ) (bits : Fin R → Bool) (hs : RationalResourceInvariant L total cursor.materialize)
    {result : RationalActiveResources L} (hr : ((rationalResourceMachine L).run R cursor bits).1 = some result) :
    InBox (fun j => (L j : ℝ)) result.resource.realAllocation ∧
      (∑ j, result.resource.realAllocation j) = total ∧
      (fractionalSet (fun j => (L j : ℝ)) result.resource.realAllocation).card ≤ 1 := by
  have hi := rationalResourceMachine_invariant L total cursor R bits hs hr
  have ht := rationalResourceMachine_terminal L cursor R bits hr
  have he := result.realView.length_eq_card
  change result.active.length = (fractionalSet (fun j => (L j : ℝ)) result.resource.realAllocation).card at he
  exact ⟨hi.1, hi.2, by omega⟩

end Blotto
