import Blotto.WordMachineCallbackCongruence
import Blotto.WordMachineSerialSourceWork
import Blotto.WordMachineSerialSourceSharpWork

/-! A source-only work bound needs uniform prices only on reachable source
states. A capped auxiliary price agrees there; the theorem bounds the original
uncapped observer. No cap or invariant test is added to production execution. -/

namespace Blotto.WordStateMachine

def serialInvariant {S α : Type*} {T : α → Type*} (I : S → Prop) : SerialState S α T → Prop
  | .source s => I s
  | .continuation _ _ => True

theorem serialInvariant_closed {S α β : Type*} {T : α → Type*} (m : WordStateMachine S α)
    (next : ∀ a, WordStateMachine (T a) β) (start : ∀ a, T a) (C : ℕ)
    (hC : ∀ a, (next a).rank (start a) ≤ C) (I : S → Prop)
    (hClosed : ∀ s, I s → (m.step s).Postcondition I (fun _ => True)) :
    ∀ cursor, serialInvariant I cursor →
      ((m.serial next start C hC).step cursor).Postcondition (serialInvariant I) (fun _ => True) := by
  intro cursor hI
  cases cursor with
  | source s =>
    have hp := hClosed s hI
    cases hs : m.step s with
    | done a =>
      cases ht : (next a).step (start a) <;>
        simp [serial, serialTransition, WordTransition.mapState, WordTransition.Postcondition, serialInvariant, hs, ht]
    | ask a b hb hab upper lower =>
      rw [hs] at hp
      simpa [serial, serialTransition, WordTransition.Postcondition, serialInvariant, hs] using hp
  | continuation a s =>
    cases ht : (next a).step s <;>
      simp [serial, serialTransition, WordTransition.mapState, WordTransition.Postcondition, serialInvariant, ht]

theorem runCachedSerialSourceWork_bound_under {S α β : Type*} {T : α → Type*} (m : WordStateMachine S α)
    (next : ∀ a, WordStateMachine (T a) β) (start : ∀ a, T a) (C : ℕ)
    (hC : ∀ a, (next a).rank (start a) ≤ C) (I : S → Prop)
    (hClosed : ∀ s, I s → (m.step s).Postcondition I (fun _ => True))
    (charge : S → ℕ) (bound : ℕ) (hCharge : ∀ s, I s → charge s ≤ bound)
    (R : ℕ) (s : S) (hI : I s) (bits : Fin R → Bool) :
    (m.serial next start C hC).runCachedCallbackWork (serialSourceCharge charge) R (.source s) bits ≤
      bound * (m.rank s + 1) := by
  let capped := fun q => min (charge q) bound
  have hEq : ∀ q : SerialState S α T, serialInvariant I q → serialSourceCharge charge q = serialSourceCharge capped q := by
    intro q hq
    cases q with
    | source q => exact (min_eq_left (hCharge q hq)).symm
    | continuation _ _ => rfl
  have hWork := (m.serial next start C hC).runCachedCallbackWork_congr (serialInvariant I)
    (serialSourceCharge charge) (serialSourceCharge capped) hEq
    (m.serialInvariant_closed next start C hC I hClosed) R (.source s) hI bits
  rw [hWork]
  exact m.runCachedSerialSourceWork_bound next start C hC capped bound (fun q => min_le_right _ _) R s bits

theorem runCachedSerialSourceWork_initial_bound_under {S α β : Type*} {T : α → Type*} (m : WordStateMachine S α)
    (next : ∀ a, WordStateMachine (T a) β) (start : ∀ a, T a) (C : ℕ)
    (hC : ∀ a, (next a).rank (start a) ≤ C) (I : S → Prop)
    (hClosed : ∀ s, I s → (m.step s).Postcondition I (fun _ => True))
    (charge : S → ℕ) (bound : ℕ) (hCharge : ∀ s, I s → charge s ≤ bound)
    (R : ℕ) (s : S) (hI : I s) (bits : Fin R → Bool) :
    (m.serial next start C hC).runCachedCallbackWork (serialSourceCharge charge) R (.source s) bits ≤
      bound * m.rank s + charge s := by
  let capped := fun q => min (charge q) bound
  have hEq : ∀ q : SerialState S α T, serialInvariant I q → serialSourceCharge charge q = serialSourceCharge capped q := by
    intro q hq
    cases q with
    | source q => exact (min_eq_left (hCharge q hq)).symm
    | continuation _ _ => rfl
  have hWork := (m.serial next start C hC).runCachedCallbackWork_congr (serialInvariant I)
    (serialSourceCharge charge) (serialSourceCharge capped) hEq
    (m.serialInvariant_closed next start C hC I hClosed) R (.source s) hI bits
  rw [hWork]
  have h := m.runCachedSerialSourceWork_initial_bound next start C hC capped bound (fun q => min_le_right _ _) R s bits
  exact h.trans (Nat.add_le_add_left (min_le_left _ _) _)

end Blotto.WordStateMachine
