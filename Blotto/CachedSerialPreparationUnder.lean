import Blotto.CachedSerialTerminalWork

/-! One-time preparation prices need only hold for reached source outputs.
The original indexed observer is retained, with no runtime clipping/test. -/

namespace Blotto.WordStateMachine

theorem serialPreparationPotential_under {S α β : Type*} {T : α → Type*} (m : WordStateMachine S α)
    (next : ∀ a, WordStateMachine (T a) β) (start : ∀ a, T a) (C : ℕ)
    (hC : ∀ a, (next a).rank (start a) ≤ C) (I : S → Prop) (P : α → Prop)
    (hSource : ∀ s, I s → (m.step s).Postcondition I P) (price : α → ℕ) (bound : ℕ)
    (hPrice : ∀ a, P a → price a ≤ bound) :
    ∀ cursor, serialHandoffInvariant I P (fun _ _ => True) cursor →
      match (m.serial next start C hC).step cursor with
      | .done _ => serialPreparationCharge m price cursor ≤ serialPreparationPotential bound cursor
      | .ask _ _ _ _ upper lower =>
        serialPreparationCharge m price cursor + serialPreparationPotential bound upper ≤ serialPreparationPotential bound cursor ∧
        serialPreparationCharge m price cursor + serialPreparationPotential bound lower ≤ serialPreparationPotential bound cursor := by
  intro cursor hCursor
  cases cursor with
  | source state =>
    have hp := hSource state hCursor
    cases hs : m.step state with
    | done value =>
      rw [hs] at hp
      have hc := hPrice value hp
      cases ht : (next value).step (start value) <;>
        simpa only [serial, serialTransition, hs, ht, WordTransition.mapState,
          serialPreparationCharge, serialPreparationPotential, Nat.add_zero, and_self] using hc
    | ask a b hb hab upper lower =>
      simp only [serial, serialTransition, hs, serialPreparationCharge, serialPreparationPotential,
        Nat.zero_add, le_refl, and_self]
  | continuation value state =>
    cases ht : (next value).step state <;>
      simp only [serial, serialTransition, ht, WordTransition.mapState, serialPreparationCharge,
        serialPreparationPotential, Nat.zero_add, le_refl, and_self]

theorem cachedSerialPreparationWork_bound_under {S α β : Type*} {T : α → Type*} (m : WordStateMachine S α)
    (next : ∀ a, WordStateMachine (T a) β) (start : ∀ a, T a) (C : ℕ)
    (hC : ∀ a, (next a).rank (start a) ≤ C) (I : S → Prop) (P : α → Prop)
    (hSource : ∀ s, I s → (m.step s).Postcondition I P) (price : α → ℕ) (bound : ℕ)
    (hPrice : ∀ a, P a → price a ≤ bound) (N : ℕ) (bits : Fin N → Bool) (state : S)
    (hI : I state) (pos : ℕ) (hpos : pos ≤ N) :
    (m.serial next start C hC).cachedCallbackWork (serialPreparationCharge m price)
      N bits (.state (.source state)) pos hpos ≤ bound := by
  have hClosed := m.serialHandoffInvariant_closed next start C hC I P (fun _ _ => True)
    hSource (fun _ _ => trivial) (fun a _ state _ => by cases (next a).step state <;> trivial)
  exact (m.serial next start C hC).cachedCallbackWork_state_potential_under
    (serialHandoffInvariant I P (fun _ _ => True)) hClosed (serialPreparationCharge m price)
    (serialPreparationPotential bound)
    (fun cursor hCursor => by
      have hp := m.serialPreparationPotential_under next start C hC I P hSource price bound hPrice cursor hCursor
      cases ht : (m.serial next start C hC).step cursor with
      | done value => rw [ht] at hp; exact hp
      | ask a b hb hab upper lower => rw [ht] at hp; exact hp)
    N bits (.source state) hI pos hpos

end Blotto.WordStateMachine
