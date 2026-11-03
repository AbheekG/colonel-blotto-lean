import Blotto.CachedWordCallbackWork
import Blotto.WordMachineSerial

/-! Source-only callback prices in a serial controller are bounded by the
source rank, independently of the continuation rank and shared bit cap. -/

namespace Blotto.WordStateMachine

def serialSourceCharge {S α : Type*} {T : α → Type*} (charge : S → ℕ) : SerialState S α T → ℕ
  | .source s => charge s
  | .continuation _ _ => 0

def serialSourcePotential {S α : Type*} {T : α → Type*} (m : WordStateMachine S α)
    (bound : ℕ) : SerialState S α T → ℕ
  | .source s => bound * (m.rank s + 1)
  | .continuation _ _ => 0

theorem serial_sourcePotential {S α β : Type*} {T : α → Type*} (m : WordStateMachine S α)
    (next : ∀ a, WordStateMachine (T a) β) (start : ∀ a, T a) (C : ℕ)
    (hC : ∀ a, (next a).rank (start a) ≤ C) (charge : S → ℕ) (bound : ℕ)
    (hCharge : ∀ s, charge s ≤ bound) :
    (m.serial next start C hC).WorkPotential (serialSourceCharge charge) (serialSourcePotential m bound) := by
  intro cursor
  cases cursor with
  | source s =>
    have hc := hCharge s
    cases hs : m.step s with
    | done a =>
      have hDone : charge s ≤ bound * (m.rank s + 1) := by nlinarith
      cases ht : (next a).step (start a) <;>
        simpa [serial, serialTransition, WordTransition.mapState, serialSourceCharge,
          serialSourcePotential, hs, ht] using hDone
    | ask a b hb hab upper lower =>
      have hp := m.progress s
      rw [hs] at hp
      have hu : charge s + bound * (m.rank upper + 1) ≤ bound * (m.rank s + 1) := by nlinarith [hp.1]
      have hl : charge s + bound * (m.rank lower + 1) ≤ bound * (m.rank s + 1) := by nlinarith [hp.2]
      simpa [serial, serialTransition, serialSourceCharge, serialSourcePotential, hs] using And.intro hu hl
  | continuation a s =>
    cases ht : (next a).step s <;>
      simp [serial, serialTransition, WordTransition.mapState, serialSourceCharge, serialSourcePotential, ht]

theorem runCachedSerialSourceWork_bound {S α β : Type*} {T : α → Type*} (m : WordStateMachine S α)
    (next : ∀ a, WordStateMachine (T a) β) (start : ∀ a, T a) (C : ℕ)
    (hC : ∀ a, (next a).rank (start a) ≤ C) (charge : S → ℕ) (bound : ℕ)
    (hCharge : ∀ s, charge s ≤ bound) (R : ℕ) (s : S) (bits : Fin R → Bool) :
    (m.serial next start C hC).runCachedCallbackWork (serialSourceCharge charge) R (.source s) bits ≤
      bound * (m.rank s + 1) :=
  (m.serial next start C hC).runCachedCallbackWork_potential (serialSourceCharge charge)
    (serialSourcePotential m bound) (m.serial_sourcePotential next start C hC charge bound hCharge) R (.source s) bits

end Blotto.WordStateMachine
