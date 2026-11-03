import Blotto.CachedSerialTerminalWork
import Blotto.CachedEmissionWork

/-! Output-only terminal charges pay at most once along a serial path.
Only reached source outputs need the price bound. Source asks and terminal asks
pay zero, and the same caller cap/current position are retained. -/

namespace Blotto.WordStateMachine

theorem serialEmissionCharge_eq {S α β : Type*} {T : α → Type*} (m : WordStateMachine S α)
    (next : ∀ a, WordStateMachine (T a) β) (start : ∀ a, T a) (C : ℕ)
    (hC : ∀ a, (next a).rank (start a) ≤ C) (price : β → ℕ) :
    serialHandoffCharge m start (fun _ => 0) (fun a => (next a).emissionCharge price) =
      (m.serial next start C hC).emissionCharge price := by
  funext cursor
  cases cursor with
  | source state =>
    cases hs : m.step state with
    | done value =>
      cases ht : (next value).step (start value) <;>
        simp only [serialHandoffCharge, emissionCharge, serial, serialTransition, hs, ht, WordTransition.mapState, Nat.zero_add]
    | ask a b hb hab upper lower =>
      simp only [serialHandoffCharge, emissionCharge, serial, serialTransition, hs]
  | continuation value state =>
    cases ht : (next value).step state <;>
      simp only [serialHandoffCharge, emissionCharge, serial, serialTransition, ht, WordTransition.mapState]

theorem serialHandoffCharge_zero_on_ask {S α β : Type*} {T : α → Type*} (m : WordStateMachine S α)
    (next : ∀ a, WordStateMachine (T a) β) (start : ∀ a, T a) (C : ℕ)
    (hC : ∀ a, (next a).rank (start a) ≤ C) (charge : ∀ a, T a → ℕ)
    (hCharge : ∀ a state, match (next a).step state with
      | .done _ => True
      | .ask _ _ _ _ _ _ => charge a state = 0) (cursor : SerialState S α T) :
    match (m.serial next start C hC).step cursor with
    | .done _ => True
    | .ask _ _ _ _ _ _ => serialHandoffCharge m start (fun _ => 0) charge cursor = 0 := by
  cases cursor with
  | source state =>
    cases hs : m.step state with
    | done value =>
      have hc := hCharge value (start value)
      cases ht : (next value).step (start value) with
      | done output => simp only [serial, serialTransition, hs, ht, WordTransition.mapState]
      | ask a b hb hab upper lower =>
        rw [ht] at hc
        simpa only [serial, serialTransition, hs, ht, WordTransition.mapState, serialHandoffCharge, Nat.zero_add] using hc
    | ask a b hb hab upper lower => simp only [serial, serialTransition, hs, serialHandoffCharge]
  | continuation value state =>
    have hc := hCharge value state
    cases ht : (next value).step state with
    | done output => simp only [serial, serialTransition, ht, WordTransition.mapState]
    | ask a b hb hab upper lower =>
      rw [ht] at hc
      simpa only [serial, serialTransition, ht, WordTransition.mapState, serialHandoffCharge] using hc

theorem serialEmissionPotential_under {S α β : Type*} {T : α → Type*} (m : WordStateMachine S α)
    (next : ∀ a, WordStateMachine (T a) β) (start : ∀ a, T a) (C : ℕ)
    (hC : ∀ a, (next a).rank (start a) ≤ C) (I : S → Prop) (P : α → Prop)
    (hSource : ∀ s, I s → (m.step s).Postcondition I P) (charge : ∀ a, T a → ℕ) (bound : ℕ)
    (hTerminal : ∀ a, P a → ∀ state, match (next a).step state with
      | .done _ => charge a state ≤ bound
      | .ask _ _ _ _ _ _ => charge a state = 0) :
    ∀ cursor, serialHandoffInvariant I P (fun _ _ => True) cursor →
      match (m.serial next start C hC).step cursor with
      | .done _ => serialHandoffCharge m start (fun _ => 0) charge cursor ≤ bound
      | .ask _ _ _ _ _ _ => serialHandoffCharge m start (fun _ => 0) charge cursor + bound ≤ bound := by
  intro cursor hCursor
  cases cursor with
  | source state =>
    have hp := hSource state hCursor
    cases hs : m.step state with
    | done value =>
      rw [hs] at hp
      have ht := hTerminal value hp (start value)
      cases hn : (next value).step (start value) with
      | done output =>
        rw [hn] at ht
        simpa only [serial, serialTransition, hs, hn, WordTransition.mapState, serialHandoffCharge, Nat.zero_add] using ht
      | ask a b hb hab upper lower =>
        rw [hn] at ht
        simp only [serial, serialTransition, hs, hn, WordTransition.mapState, serialHandoffCharge, Nat.zero_add, ht, le_refl]
    | ask a b hb hab upper lower =>
      simp only [serial, serialTransition, hs, serialHandoffCharge, Nat.zero_add, le_refl]
  | continuation value state =>
    have ht := hTerminal value hCursor.1 state
    cases hn : (next value).step state with
    | done output =>
      rw [hn] at ht
      simpa only [serial, serialTransition, hn, WordTransition.mapState, serialHandoffCharge] using ht
    | ask a b hb hab upper lower =>
      rw [hn] at ht
      simp only [serial, serialTransition, hn, WordTransition.mapState, serialHandoffCharge, ht, Nat.zero_add, le_refl]

theorem cachedSerialEmissionWork_bound_under {S α β : Type*} {T : α → Type*} (m : WordStateMachine S α)
    (next : ∀ a, WordStateMachine (T a) β) (start : ∀ a, T a) (C : ℕ)
    (hC : ∀ a, (next a).rank (start a) ≤ C) (I : S → Prop) (P : α → Prop)
    (hSource : ∀ s, I s → (m.step s).Postcondition I P) (charge : ∀ a, T a → ℕ) (bound : ℕ)
    (hTerminal : ∀ a, P a → ∀ state, match (next a).step state with
      | .done _ => charge a state ≤ bound
      | .ask _ _ _ _ _ _ => charge a state = 0)
    (N : ℕ) (bits : Fin N → Bool) (state : S) (hI : I state) (pos : ℕ) (hpos : pos ≤ N) :
    (m.serial next start C hC).cachedCallbackWork (serialHandoffCharge m start (fun _ => 0) charge)
      N bits (.state (.source state)) pos hpos ≤ bound := by
  have hClosed := m.serialHandoffInvariant_closed next start C hC I P (fun _ _ => True)
    hSource (fun _ _ => trivial) (fun a _ state _ => by cases (next a).step state <;> trivial)
  exact (m.serial next start C hC).cachedCallbackWork_state_potential_under
    (serialHandoffInvariant I P (fun _ _ => True)) hClosed (serialHandoffCharge m start (fun _ => 0) charge)
    (fun _ => bound)
    (fun cursor hCursor => by
      have hp := m.serialEmissionPotential_under next start C hC I P hSource charge bound hTerminal cursor hCursor
      cases ht : (m.serial next start C hC).step cursor with
      | done output => rw [ht] at hp; exact hp
      | ask a b hb hab upper lower => rw [ht] at hp; exact ⟨hp, hp⟩)
    N bits (.source state) hI pos hpos

end Blotto.WordStateMachine
