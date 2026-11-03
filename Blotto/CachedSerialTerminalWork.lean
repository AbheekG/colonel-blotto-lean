import Blotto.CachedCallbackPotentialUnder
import Blotto.CachedSerialHandoffWork

/-! Terminal callback work is bounded by terminal rank, independently of
source length. A closed source/output/continuation invariant carries only the
reached price hypotheses. The shared reader and its current position are kept. -/

namespace Blotto.WordStateMachine

def serialHandoffInvariant {S α : Type*} {T : α → Type*} (I : S → Prop) (P : α → Prop)
    (J : ∀ a, T a → Prop) : SerialState S α T → Prop
  | .source s => I s
  | .continuation a t => P a ∧ J a t

theorem serialHandoffInvariant_closed {S α β : Type*} {T : α → Type*} (m : WordStateMachine S α)
    (next : ∀ a, WordStateMachine (T a) β) (start : ∀ a, T a) (C : ℕ)
    (hC : ∀ a, (next a).rank (start a) ≤ C) (I : S → Prop) (P : α → Prop) (J : ∀ a, T a → Prop)
    (hSource : ∀ s, I s → (m.step s).Postcondition I P) (hStart : ∀ a, P a → J a (start a))
    (hTerminal : ∀ a, P a → ∀ t, J a t → ((next a).step t).Postcondition (J a) (fun _ => True)) :
    ∀ cursor, serialHandoffInvariant I P J cursor →
      ((m.serial next start C hC).step cursor).Postcondition (serialHandoffInvariant I P J) (fun _ => True) := by
  intro cursor hCursor
  cases cursor with
  | source s =>
    have hp := hSource s hCursor
    cases hs : m.step s with
    | done value =>
      rw [hs] at hp
      have hn := hTerminal value hp (start value) (hStart value hp)
      cases ht : (next value).step (start value) with
      | done output => simp [serial, serialTransition, hs, ht, WordTransition.mapState, WordTransition.Postcondition]
      | ask a b hb hab upper lower =>
        rw [ht] at hn
        simpa only [serial, serialTransition, hs, ht, WordTransition.mapState, WordTransition.Postcondition, serialHandoffInvariant]
          using And.intro (And.intro hp hn.1) (And.intro hp hn.2)
    | ask a b hb hab upper lower =>
      rw [hs] at hp
      simpa only [serial, serialTransition, hs, WordTransition.Postcondition, serialHandoffInvariant] using hp
  | continuation value t =>
    have hn := hTerminal value hCursor.1 t hCursor.2
    cases ht : (next value).step t with
    | done output => simp [serial, serialTransition, ht, WordTransition.mapState, WordTransition.Postcondition]
    | ask a b hb hab upper lower =>
      rw [ht] at hn
      simpa only [serial, serialTransition, ht, WordTransition.mapState, WordTransition.Postcondition, serialHandoffInvariant]
        using And.intro (And.intro hCursor.1 hn.1) (And.intro hCursor.1 hn.2)

def serialTerminalCallbackPotential {S α β : Type*} {T : α → Type*}
    (next : ∀ a, WordStateMachine (T a) β) (C bound : ℕ) : SerialState S α T → ℕ
  | .source _ => bound * (C + 1)
  | .continuation a t => bound * ((next a).rank t + 1)

theorem serialTerminalCallbackPotential_under {S α β : Type*} {T : α → Type*} (m : WordStateMachine S α)
    (next : ∀ a, WordStateMachine (T a) β) (start : ∀ a, T a) (C : ℕ)
    (hC : ∀ a, (next a).rank (start a) ≤ C) (I : S → Prop) (P : α → Prop) (J : ∀ a, T a → Prop)
    (hSource : ∀ s, I s → (m.step s).Postcondition I P) (hStart : ∀ a, P a → J a (start a))
    (charge : ∀ a, T a → ℕ) (bound : ℕ) (hCharge : ∀ a, P a → ∀ t, J a t → charge a t ≤ bound) :
    ∀ cursor, serialHandoffInvariant I P J cursor →
      match (m.serial next start C hC).step cursor with
      | .done _ => serialHandoffCharge m start (fun _ => 0) charge cursor ≤ serialTerminalCallbackPotential next C bound cursor
      | .ask _ _ _ _ upper lower =>
        serialHandoffCharge m start (fun _ => 0) charge cursor + serialTerminalCallbackPotential next C bound upper ≤ serialTerminalCallbackPotential next C bound cursor ∧
        serialHandoffCharge m start (fun _ => 0) charge cursor + serialTerminalCallbackPotential next C bound lower ≤ serialTerminalCallbackPotential next C bound cursor := by
  intro cursor hCursor
  cases cursor with
  | source s =>
    have hp := hSource s hCursor
    cases hs : m.step s with
    | done value =>
      rw [hs] at hp
      have hc := hCharge value hp (start value) (hStart value hp)
      have hr := hC value
      have hn := (next value).progress (start value)
      cases ht : (next value).step (start value) with
      | done output =>
        have hw : charge value (start value) ≤ bound * (C + 1) := by nlinarith
        simpa only [serial, serialTransition, hs, ht, WordTransition.mapState, serialHandoffCharge, serialTerminalCallbackPotential, Nat.zero_add] using hw
      | ask a b hb hab upper lower =>
        rw [ht] at hn
        have hu : charge value (start value) + bound * ((next value).rank upper + 1) ≤ bound * (C + 1) := by nlinarith [hn.1]
        have hl : charge value (start value) + bound * ((next value).rank lower + 1) ≤ bound * (C + 1) := by nlinarith [hn.2]
        simpa only [serial, serialTransition, hs, ht, WordTransition.mapState, serialHandoffCharge, serialTerminalCallbackPotential, Nat.zero_add] using And.intro hu hl
    | ask a b hb hab upper lower =>
      simp only [serial, serialTransition, hs, serialHandoffCharge, serialTerminalCallbackPotential, Nat.zero_add, le_refl, and_self]
  | continuation value t =>
    have hc := hCharge value hCursor.1 t hCursor.2
    have hn := (next value).progress t
    cases ht : (next value).step t with
    | done output =>
      have hw : charge value t ≤ bound * ((next value).rank t + 1) := by nlinarith
      simpa only [serial, serialTransition, ht, WordTransition.mapState, serialHandoffCharge, serialTerminalCallbackPotential] using hw
    | ask a b hb hab upper lower =>
      rw [ht] at hn
      have hu : charge value t + bound * ((next value).rank upper + 1) ≤ bound * ((next value).rank t + 1) := by nlinarith [hn.1]
      have hl : charge value t + bound * ((next value).rank lower + 1) ≤ bound * ((next value).rank t + 1) := by nlinarith [hn.2]
      simpa only [serial, serialTransition, ht, WordTransition.mapState, serialHandoffCharge, serialTerminalCallbackPotential] using And.intro hu hl

theorem cachedSerialTerminalWork_bound_under {S α β : Type*} {T : α → Type*} (m : WordStateMachine S α)
    (next : ∀ a, WordStateMachine (T a) β) (start : ∀ a, T a) (C : ℕ)
    (hC : ∀ a, (next a).rank (start a) ≤ C) (I : S → Prop) (P : α → Prop) (J : ∀ a, T a → Prop)
    (hSource : ∀ s, I s → (m.step s).Postcondition I P) (hStart : ∀ a, P a → J a (start a))
    (hTerminal : ∀ a, P a → ∀ t, J a t → ((next a).step t).Postcondition (J a) (fun _ => True))
    (charge : ∀ a, T a → ℕ) (bound : ℕ) (hCharge : ∀ a, P a → ∀ t, J a t → charge a t ≤ bound)
    (N : ℕ) (bits : Fin N → Bool) (state : S) (hI : I state) (pos : ℕ) (hpos : pos ≤ N) :
    (m.serial next start C hC).cachedCallbackWork (serialHandoffCharge m start (fun _ => 0) charge)
      N bits (.state (.source state)) pos hpos ≤ bound * (C + 1) :=
  (m.serial next start C hC).cachedCallbackWork_state_potential_under (serialHandoffInvariant I P J)
    (m.serialHandoffInvariant_closed next start C hC I P J hSource hStart hTerminal)
    (serialHandoffCharge m start (fun _ => 0) charge) (serialTerminalCallbackPotential next C bound)
    (fun cursor hCursor => by
      have hp := m.serialTerminalCallbackPotential_under next start C hC I P J hSource hStart charge bound hCharge cursor hCursor
      cases hs : (m.serial next start C hC).step cursor with
      | done value => rw [hs] at hp; exact hp
      | ask a b hb hab upper lower => rw [hs] at hp; exact hp)
    N bits (.source state) hI pos hpos

end Blotto.WordStateMachine
