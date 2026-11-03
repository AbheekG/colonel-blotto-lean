import Blotto.WordMachineSerialSourceWork

/-! The first source callback pays its actual price. A zero-price initial
callback removes the extra rank allowance, as in selected resource stores. -/

namespace Blotto.WordStateMachine

def serialSourceResidualPotential {S α : Type*} {T : α → Type*} (m : WordStateMachine S α)
    (charge : S → ℕ) (bound : ℕ) : SerialState S α T → ℕ
  | .source s => bound * m.rank s + charge s
  | .continuation _ _ => 0

theorem serial_sourceResidualPotential {S α β : Type*} {T : α → Type*} (m : WordStateMachine S α)
    (next : ∀ a, WordStateMachine (T a) β) (start : ∀ a, T a) (C : ℕ)
    (hC : ∀ a, (next a).rank (start a) ≤ C) (charge : S → ℕ) (bound : ℕ)
    (hCharge : ∀ s, charge s ≤ bound) :
    (m.serial next start C hC).WorkPotential (serialSourceCharge charge) (serialSourceResidualPotential m charge bound) := by
  intro cursor
  cases cursor with
  | source s =>
    cases hs : m.step s with
    | done a =>
      cases ht : (next a).step (start a) <;>
        simp [serial, serialTransition, WordTransition.mapState, serialSourceCharge,
          serialSourceResidualPotential, hs, ht]
    | ask a b hb hab upper lower =>
      have hp := m.progress s
      rw [hs] at hp
      have hu : charge s + (bound * m.rank upper + charge upper) ≤ bound * m.rank s + charge s := by
        nlinarith [hp.1, hCharge upper]
      have hl : charge s + (bound * m.rank lower + charge lower) ≤ bound * m.rank s + charge s := by
        nlinarith [hp.2, hCharge lower]
      simpa [serial, serialTransition, serialSourceCharge, serialSourceResidualPotential, hs] using And.intro hu hl
  | continuation a s =>
    cases ht : (next a).step s <;>
      simp [serial, serialTransition, WordTransition.mapState, serialSourceCharge, serialSourceResidualPotential, ht]

theorem runCachedSerialSourceWork_initial_bound {S α β : Type*} {T : α → Type*} (m : WordStateMachine S α)
    (next : ∀ a, WordStateMachine (T a) β) (start : ∀ a, T a) (C : ℕ)
    (hC : ∀ a, (next a).rank (start a) ≤ C) (charge : S → ℕ) (bound : ℕ)
    (hCharge : ∀ s, charge s ≤ bound) (R : ℕ) (s : S) (bits : Fin R → Bool) :
    (m.serial next start C hC).runCachedCallbackWork (serialSourceCharge charge) R (.source s) bits ≤
      bound * m.rank s + charge s :=
  (m.serial next start C hC).runCachedCallbackWork_potential (serialSourceCharge charge)
    (serialSourceResidualPotential m charge bound) (m.serial_sourceResidualPotential next start C hC charge bound hCharge)
    R (.source s) bits

end Blotto.WordStateMachine
