import Blotto.CachedCallbackReindex
import Blotto.SharedResourceCallbackWork
import Blotto.WordMachineSerialPreparationWork

/-! A serial completion combines its one-time preparation price with the
first terminal callback price. Later callbacks charge only that continuation.
The equality holds for arbitrary prices and the current reader position. -/

namespace Blotto.WordStateMachine

def serialHandoffCharge {S α : Type*} {T : α → Type*} (m : WordStateMachine S α)
    (start : ∀ a, T a) (cost : α → ℕ) (terminalCharge : ∀ a, T a → ℕ) : SerialState S α T → ℕ
  | .source s => match m.step s with
    | .done a => cost a + terminalCharge a (start a)
    | .ask _ _ _ _ _ _ => 0
  | .continuation a s => terminalCharge a s

theorem serialHandoffCharge_zeroTerminal {S α : Type*} {T : α → Type*} (m : WordStateMachine S α)
    (start : ∀ a, T a) (cost : α → ℕ) :
    serialHandoffCharge m start cost (fun _ _ => 0) = serialPreparationCharge m cost := by
  funext state
  cases state with
  | source s => cases hs : m.step s <;> simp only [serialHandoffCharge, serialPreparationCharge, hs, Nat.add_zero]
  | continuation a s => rfl

theorem cachedCallbackTailWork_step_eq {S α : Type*} (m : WordStateMachine S α) (charge : S → ℕ)
    (s t : S) (hStep : m.step s = m.step t) (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) :
    m.cachedCallbackTailWork charge N bits s pos hpos = m.cachedCallbackTailWork charge N bits t pos hpos := by
  unfold cachedCallbackTailWork
  rw [hStep]

theorem cachedSerialContinuationHandoffWork {S α β : Type*} {T : α → Type*} (m : WordStateMachine S α)
    (next : ∀ a, WordStateMachine (T a) β) (start : ∀ a, T a) (C : ℕ)
    (hC : ∀ a, (next a).rank (start a) ≤ C) (cost : α → ℕ) (terminalCharge : ∀ a, T a → ℕ)
    (value : α) (state : T value) (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) :
    (m.serial next start C hC).cachedCallbackWork (serialHandoffCharge m start cost terminalCharge)
      N bits (.state (.continuation value state)) pos hpos =
      (next value).cachedCallbackWork (terminalCharge value) N bits (.state state) pos hpos :=
  (next value).cachedCallbackWork_reindex (m.serial next start C hC)
    (fun s => (SerialState.continuation value s : SerialState S α T))
    (fun _ => rfl) (terminalCharge value) (serialHandoffCharge m start cost terminalCharge)
    (fun _ => rfl) N bits (.state state) pos hpos

theorem cachedSerialDoneHandoffWork {S α β : Type*} {T : α → Type*} (m : WordStateMachine S α)
    (next : ∀ a, WordStateMachine (T a) β) (start : ∀ a, T a) (C : ℕ)
    (hC : ∀ a, (next a).rank (start a) ≤ C) (cost : α → ℕ) (terminalCharge : ∀ a, T a → ℕ)
    (state : S) (value : α) (hDone : m.step state = .done value)
    (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) :
    (m.serial next start C hC).cachedCallbackWork (serialHandoffCharge m start cost terminalCharge)
      N bits (.state (.source state)) pos hpos =
      cost value + (next value).cachedCallbackWork (terminalCharge value) N bits (.state (start value)) pos hpos := by
  let target := m.serial next start C hC
  let charge := serialHandoffCharge m start cost terminalCharge
  have hStep : target.step (.source state) = target.step (.continuation value (start value)) := by
    simp only [target, serial, serialTransition, hDone]
  have hTail := target.cachedCallbackTailWork_step_eq charge (.source state)
    (.continuation value (start value)) hStep N bits pos hpos
  calc
    target.cachedCallbackWork charge N bits (.state (.source state)) pos hpos =
        cost value + target.cachedCallbackWork charge N bits (.state (.continuation value (start value))) pos hpos := by
      rw [target.cachedCallbackWork_state, target.cachedCallbackWork_state, hTail]
      simp only [charge, serialHandoffCharge, hDone]
      omega
    _ = _ := by rw [m.cachedSerialContinuationHandoffWork next start C hC cost terminalCharge]

end Blotto.WordStateMachine
