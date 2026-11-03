import Blotto.CachedSerialTerminalWork

/-! Serial step evaluation reconstructs `next` at each terminal callback, and
evaluates `start` at the source handoff. An equal price for the two factories
pays twice at handoff and once per later callback. The bound is independent
of source length and includes cap exhaustion. No factory caching is assumed. -/

namespace Blotto.WordStateMachine

def serialFactoryCharge {S α : Type*} {T : α → Type*} (m : WordStateMachine S α)
    (start : ∀ a, T a) (price : α → ℕ) : SerialState S α T → ℕ :=
  serialHandoffCharge m start price (fun a _ => price a)

theorem serialFactoryCharge_source_done {S α : Type*} {T : α → Type*} (m : WordStateMachine S α)
    (start : ∀ a, T a) (price : α → ℕ) (state : S) (value : α) (hDone : m.step state = .done value) :
    (serialFactoryCharge m start price : SerialState S α T → ℕ) (.source state) = 2 * price value := by
  simp only [serialFactoryCharge, serialHandoffCharge, hDone]
  omega

theorem serialFactoryCharge_continuation {S α : Type*} {T : α → Type*} (m : WordStateMachine S α)
    (start : ∀ a, T a) (price : α → ℕ) (value : α) (state : T value) :
    (serialFactoryCharge m start price : SerialState S α T → ℕ) (.continuation value state) = price value := rfl

def serialFactoryPotential {S α β : Type*} {T : α → Type*}
    (next : ∀ a, WordStateMachine (T a) β) (C bound : ℕ) : SerialState S α T → ℕ
  | .source _ => bound * (C + 2)
  | .continuation a state => bound * ((next a).rank state + 1)

theorem serialFactoryPotential_under {S α β : Type*} {T : α → Type*} (m : WordStateMachine S α)
    (next : ∀ a, WordStateMachine (T a) β) (start : ∀ a, T a) (C : ℕ)
    (hC : ∀ a, (next a).rank (start a) ≤ C) (I : S → Prop) (P : α → Prop)
    (hSource : ∀ s, I s → (m.step s).Postcondition I P) (price : α → ℕ) (bound : ℕ)
    (hPrice : ∀ a, P a → price a ≤ bound) :
    ∀ cursor, serialHandoffInvariant I P (fun _ _ => True) cursor →
      match (m.serial next start C hC).step cursor with
      | .done _ => serialFactoryCharge m start price cursor ≤ serialFactoryPotential next C bound cursor
      | .ask _ _ _ _ upper lower =>
        serialFactoryCharge m start price cursor + serialFactoryPotential next C bound upper ≤ serialFactoryPotential next C bound cursor ∧
        serialFactoryCharge m start price cursor + serialFactoryPotential next C bound lower ≤ serialFactoryPotential next C bound cursor := by
  intro cursor hCursor
  cases cursor with
  | source state =>
    have hp := hSource state hCursor
    cases hs : m.step state with
    | done value =>
      rw [hs] at hp
      have hc := hPrice value hp
      have hr := hC value
      have hn := (next value).progress (start value)
      cases ht : (next value).step (start value) with
      | done output =>
        have hw : 2 * price value ≤ bound * (C + 2) := by nlinarith
        simpa only [serial, serialTransition, hs, ht, WordTransition.mapState,
          serialFactoryCharge, serialHandoffCharge, serialFactoryPotential, two_mul] using hw
      | ask a b hb hab upper lower =>
        rw [ht] at hn
        have hu : 2 * price value + bound * ((next value).rank upper + 1) ≤ bound * (C + 2) := by nlinarith [hn.1]
        have hl : 2 * price value + bound * ((next value).rank lower + 1) ≤ bound * (C + 2) := by nlinarith [hn.2]
        simpa only [serial, serialTransition, hs, ht, WordTransition.mapState,
          serialFactoryCharge, serialHandoffCharge, serialFactoryPotential, two_mul] using And.intro hu hl
    | ask a b hb hab upper lower =>
      simp only [serial, serialTransition, hs, serialFactoryCharge, serialHandoffCharge,
        serialFactoryPotential, Nat.zero_add, le_refl, and_self]
  | continuation value state =>
    have hc := hPrice value hCursor.1
    have hn := (next value).progress state
    cases ht : (next value).step state with
    | done output =>
      have hw : price value ≤ bound * ((next value).rank state + 1) := by nlinarith
      simpa only [serial, serialTransition, ht, WordTransition.mapState,
        serialFactoryCharge, serialHandoffCharge, serialFactoryPotential] using hw
    | ask a b hb hab upper lower =>
      rw [ht] at hn
      have hu : price value + bound * ((next value).rank upper + 1) ≤ bound * ((next value).rank state + 1) := by nlinarith [hn.1]
      have hl : price value + bound * ((next value).rank lower + 1) ≤ bound * ((next value).rank state + 1) := by nlinarith [hn.2]
      simpa only [serial, serialTransition, ht, WordTransition.mapState,
        serialFactoryCharge, serialHandoffCharge, serialFactoryPotential] using And.intro hu hl

theorem cachedSerialFactoryWork_bound_under {S α β : Type*} {T : α → Type*} (m : WordStateMachine S α)
    (next : ∀ a, WordStateMachine (T a) β) (start : ∀ a, T a) (C : ℕ)
    (hC : ∀ a, (next a).rank (start a) ≤ C) (I : S → Prop) (P : α → Prop)
    (hSource : ∀ s, I s → (m.step s).Postcondition I P) (price : α → ℕ) (bound : ℕ)
    (hPrice : ∀ a, P a → price a ≤ bound) (N : ℕ) (bits : Fin N → Bool) (state : S)
    (hI : I state) (pos : ℕ) (hpos : pos ≤ N) :
    (m.serial next start C hC).cachedCallbackWork (serialFactoryCharge m start price)
      N bits (.state (.source state)) pos hpos ≤ bound * (C + 2) := by
  have hClosed := m.serialHandoffInvariant_closed next start C hC I P (fun _ _ => True)
    hSource (fun _ _ => trivial) (fun a _ state _ => by cases (next a).step state <;> trivial)
  exact (m.serial next start C hC).cachedCallbackWork_state_potential_under
    (serialHandoffInvariant I P (fun _ _ => True)) hClosed (serialFactoryCharge m start price)
    (serialFactoryPotential next C bound)
    (fun cursor hCursor => by
      have hp := m.serialFactoryPotential_under next start C hC I P hSource price bound hPrice cursor hCursor
      cases ht : (m.serial next start C hC).step cursor with
      | done output => rw [ht] at hp; exact hp
      | ask a b hb hab upper lower => rw [ht] at hp; exact hp)
    N bits (.source state) hI pos hpos

theorem cachedSerialFactoryCount_bound {S α β : Type*} {T : α → Type*} (m : WordStateMachine S α)
    (next : ∀ a, WordStateMachine (T a) β) (start : ∀ a, T a) (C : ℕ)
    (hC : ∀ a, (next a).rank (start a) ≤ C) (N : ℕ) (bits : Fin N → Bool) (state : S) (pos : ℕ) (hpos : pos ≤ N) :
    (m.serial next start C hC).cachedCallbackWork (serialFactoryCharge m start (fun _ => 1))
      N bits (.state (.source state)) pos hpos ≤ C + 2 := by
  have hSource : ∀ s, True → (m.step s).Postcondition (fun _ => True) (fun _ => True) := by
    intro s _
    cases m.step s <;> trivial
  simpa only [Nat.one_mul] using m.cachedSerialFactoryWork_bound_under next start C hC
    (fun _ => True) (fun _ => True) hSource (fun _ => 1) 1 (fun _ _ => le_refl 1)
    N bits state trivial pos hpos

end Blotto.WordStateMachine
