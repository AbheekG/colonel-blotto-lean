import Blotto.WordMachineWorkPotential
import Blotto.WordMachineSerial

/-! Serial execution pays output-dependent preparation only at the source's
completion. Its continuation never returns to the source. The work potential
proves this one-time bound for all bit packets and caps, including zero cap. -/

namespace Blotto.WordStateMachine

def serialPreparationCharge {S α : Type*} {T : α → Type*} (m : WordStateMachine S α)
    (cost : α → ℕ) : SerialState S α T → ℕ
  | .source s => match m.step s with
    | .done a => cost a
    | .ask _ _ _ _ _ _ => 0
  | .continuation _ _ => 0

def serialPreparationPotential {S α : Type*} {T : α → Type*} (bound : ℕ) : SerialState S α T → ℕ
  | .source _ => bound
  | .continuation _ _ => 0

theorem serial_preparationPotential {S α β : Type*} {T : α → Type*} (m : WordStateMachine S α)
    (next : ∀ a, WordStateMachine (T a) β) (start : ∀ a, T a) (C : ℕ)
    (hC : ∀ a, (next a).rank (start a) ≤ C) (cost : α → ℕ) (bound : ℕ)
    (hCost : ∀ a, cost a ≤ bound) :
    (m.serial next start C hC).WorkPotential (serialPreparationCharge m cost) (serialPreparationPotential bound) := by
  intro cursor
  cases cursor with
  | source s =>
    cases hs : m.step s with
    | done a =>
      cases ht : (next a).step (start a) <;>
        simpa [serial, serialTransition, WordTransition.mapState, serialPreparationCharge,
          serialPreparationPotential, hs, ht] using hCost a
    | ask a b hb hab upper lower =>
      simp [serial, serialTransition, serialPreparationCharge, serialPreparationPotential, hs]
  | continuation a s =>
    cases ht : (next a).step s <;>
      simp [serial, serialTransition, WordTransition.mapState, serialPreparationCharge, serialPreparationPotential, ht]

def runSerialPreparationWork {S α β : Type*} {T : α → Type*} (m : WordStateMachine S α)
    (next : ∀ a, WordStateMachine (T a) β) (start : ∀ a, T a) (C : ℕ)
    (hC : ∀ a, (next a).rank (start a) ≤ C) (cost : α → ℕ)
    (R : ℕ) (s : S) (bits : Fin R → Bool) : ℕ :=
  (m.serial next start C hC).runCallbackWork (serialPreparationCharge m cost) R (.source s) bits

theorem runSerialPreparationWork_bound {S α β : Type*} {T : α → Type*} (m : WordStateMachine S α)
    (next : ∀ a, WordStateMachine (T a) β) (start : ∀ a, T a) (C : ℕ)
    (hC : ∀ a, (next a).rank (start a) ≤ C) (cost : α → ℕ) (bound : ℕ)
    (hCost : ∀ a, cost a ≤ bound) (R : ℕ) (s : S) (bits : Fin R → Bool) :
    m.runSerialPreparationWork next start C hC cost R s bits ≤ bound :=
  (m.serial next start C hC).runCallbackWork_potential (serialPreparationCharge m cost)
    (serialPreparationPotential bound) (m.serial_preparationPotential next start C hC cost bound hCost) R (.source s) bits

end Blotto.WordStateMachine
